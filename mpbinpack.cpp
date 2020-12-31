#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string>
#include <vector>
#include <algorithm>
#include <cctype>
#include "external/tinyxml2/tinyxml2.h"
#include "external/zlib/zlib.h"

std::string xml_path;
std::string bin_path;
std::string header_path;

void PrintUsage(char *prog_name)
{
    printf("Usage: %s xml_file [-o bin_path] [-h header_path]\n", prog_name);
    exit(1);
}

void PrintError(const char *fmt, ...)
{
    va_list args;
    va_start(args, fmt);
    vfprintf(stderr, fmt, args);
    exit(1);
    va_end(args);
}

void ParseOptions(int argc, char **argv)
{
    if (argc == 1) {
        PrintUsage(argv[0]);
    }
    xml_path = argv[1];
    bin_path = xml_path.substr(0, xml_path.find_last_of('.'))+".bin";
    header_path = "";
    for (int i = 2; i < argc; i++) {
        if (argv[i][0] == '-') {
            switch (argv[i][1]) {
                case 'o':
                    if (++i == argc) {
                        PrintUsage(argv[0]);
                    }
                    bin_path = argv[i];
                    break;

                case 'h':
                    if (++i == argc) {
                        PrintUsage(argv[0]);
                    }
                    header_path = argv[i];
                    break;

                default:
                    PrintUsage(argv[0]);
                    break;
            }
        }
    }
}

void PrintXmlError(tinyxml2::XMLError error_code)
{
    if (error_code != tinyxml2::XML_SUCCESS) {
        PrintError("tinyxml2 Error %d.\n", error_code);
    }
}

void WriteU8(FILE *file, uint8_t value)
{
    fwrite(&value, 1, 1, file);
}

void WriteS8(FILE *file, int8_t value)
{
    fwrite(&value, 1, 1, file);
}

void WriteU16(FILE *file, uint16_t value)
{
    uint8_t temp[2];
    temp[0] = value >> 8;
    temp[1] = value & 0xFF;
    fwrite(temp, 2, 1, file);
}

void WriteS16(FILE *file, int16_t value)
{
    int8_t temp[2];
    temp[0] = value >> 8;
    temp[1] = value & 0xFF;
    fwrite(temp, 2, 1, file);
}

void WriteU32(FILE *file, uint32_t value)
{
    uint8_t temp[4];
    temp[0] = value >> 24;
    temp[1] = (value >> 16) & 0xFF;
    temp[2] = (value >> 8) & 0xFF;
    temp[3] = value & 0xFF;
    fwrite(temp, 4, 1, file);
}

void WriteS32(FILE *file, int32_t value)
{
    int8_t temp[4];
    temp[0] = value >> 24;
    temp[1] = (value >> 16) & 0xFF;
    temp[2] = (value >> 8) & 0xFF;
    temp[3] = value & 0xFF;
    fwrite(temp, 4, 1, file);
}

void WriteFloat(FILE *file, float value)
{
    WriteS32(file, *(int32_t *)&value);
}

#define N 1024   /* size of ring buffer */   
#define F 66   /* upper limit for match_length */   
#define THRESHOLD 2 /* encode string into position and length  if match_length is greater than this */
#define NIL  N /* index for root of binary search trees */   

uint8_t text_buf[N + F - 1];    /* ring buffer of size N,
        with extra F-1 bytes to facilitate string comparison */
int match_position, match_length,  /* of longest match.  These are
                        set by the InsertNode() procedure. */
    lson[N + 1], rson[N + 257], dad[N + 1];  /* left & right children &
            parents -- These constitute binary search trees. */

void InitTree(void)  /* initialize trees */
{
    int  i;

    /* For i = 0 to N - 1, rson[i] and lson[i] will be the right and
       left children of node i.  These nodes need not be initialized.
       Also, dad[i] is the parent of node i.  These are initialized to
       NIL (= N), which stands for 'not used.'
       For i = 0 to 255, rson[N + i + 1] is the root of the tree
       for strings that begin with character i.  These are initialized
       to NIL.  Note there are 256 trees. */

    for (i = N + 1; i <= N + 256; i++) rson[i] = NIL;
    for (i = 0; i < N; i++) dad[i] = NIL;
}

void InsertNode(int r)
/* Inserts string of length F, text_buf[r..r+F-1], into one of the
   trees (text_buf[r]'th tree) and returns the longest-match position
   and length via the global variables match_position and match_length.
   If match_length = F, then removes the old node in favor of the new
   one, because the old one will be deleted sooner.
   Note r plays double role, as tree node and position in buffer. */
{
    int  i, p, cmp;
    uint8_t *key;

    cmp = 1;  key = &text_buf[r];  p = N + 1 + key[0];
    rson[r] = lson[r] = NIL;  match_length = 0;
    for (; ; ) {
        if (cmp >= 0) {
            if (rson[p] != NIL) p = rson[p];
            else { rson[p] = r;  dad[r] = p;  return; }
        }
        else {
            if (lson[p] != NIL) p = lson[p];
            else { lson[p] = r;  dad[r] = p;  return; }
        }
        for (i = 1; i < F; i++)
            if ((cmp = key[i] - text_buf[p + i]) != 0)  break;
        if (i > match_length) {
            match_position = p;
            if ((match_length = i) >= F)  break;
        }
    }
    dad[r] = dad[p];  lson[r] = lson[p];  rson[r] = rson[p];
    dad[lson[p]] = r;  dad[rson[p]] = r;
    if (rson[dad[p]] == p) rson[dad[p]] = r;
    else                   lson[dad[p]] = r;
    dad[p] = NIL;  /* remove p */
}

void DeleteNode(int p)  /* deletes node p from tree */
{
    int  q;

    if (dad[p] == NIL) return;  /* not in tree */
    if (rson[p] == NIL) q = lson[p];
    else if (lson[p] == NIL) q = rson[p];
    else {
        q = lson[p];
        if (rson[q] != NIL) {
            do { q = rson[q]; } while (rson[q] != NIL);
            rson[dad[q]] = lson[q];  dad[lson[q]] = dad[q];
            lson[q] = lson[p];  dad[lson[p]] = q;
        }
        rson[q] = rson[p];  dad[rson[p]] = q;
    }
    dad[q] = dad[p];
    if (rson[dad[p]] == p) rson[dad[p]] = q;  else lson[dad[p]] = q;
    dad[p] = NIL;
}

uint32_t CompressLzss(FILE *dst_file, FILE *src_file)
{
    int  i, c, len, r, s, last_match_length, code_buf_ptr;
    uint8_t code_buf[17], mask;
    uint32_t codesize = 0;

    InitTree();  /* initialize trees */
    code_buf[0] = 0;  /* code_buf[1..16] saves eight units of code, and
            code_buf[0] works as eight flags, "1" representing that the unit
            is an unencoded letter (1 byte), "0" a position-and-length pair
            (2 bytes).  Thus, eight units require at most 16 bytes of code. */
    code_buf_ptr = mask = 1;
    s = 0;  r = N - F;
    for (i = s; i < r; i++) text_buf[i] = '\0';  /* Clear the buffer with
            any character that will appear often. */
    for (len = 0; len < F && (c = getc(src_file)) != EOF; len++)
        text_buf[r + len] = c;  /* Read F bytes into the last F bytes of
                the buffer */
    if (len == 0) return 0;  /* text of size zero */
    for (i = 1; i <= F; i++) InsertNode(r - i);  /* Insert the F strings,
            each of which begins with one or more 'space' characters.  Note
            the order in which these strings are inserted.  This way,
            degenerate trees will be less likely to occur. */
    InsertNode(r);  /* Finally, insert the whole string just read.  The
            global variables match_length and match_position are set. */
    do {
        if (match_length > len) match_length = len;  /* match_length
                may be spuriously long near the end of text. */
        if (match_length <= THRESHOLD) {
            match_length = 1;  /* Not long enough match.  Send one byte. */
            code_buf[0] |= mask;  /* 'send one byte' flag */
            code_buf[code_buf_ptr++] = text_buf[r];  /* Send uncoded. */
        }
        else {
            code_buf[code_buf_ptr++] = (uint8_t)match_position;
            code_buf[code_buf_ptr++] = (uint8_t)
                (((match_position >> 2) & 0xC0)
                    | (match_length - (THRESHOLD + 1)));  /* Send position and
                                  length pair. Note match_length > THRESHOLD. */
        }
        if ((mask <<= 1) == 0) {  /* Shift mask left one bit. */
            for (i = 0; i < code_buf_ptr; i++)  /* Send at most 8 units of */
                putc(code_buf[i], dst_file);     /* code together */
            codesize += code_buf_ptr;
            code_buf[0] = 0;  code_buf_ptr = mask = 1;
        }
        last_match_length = match_length;
        for (i = 0; i < last_match_length &&
            (c = getc(src_file)) != EOF; i++) {
            DeleteNode(s);          /* Delete old strings and */
            text_buf[s] = c;        /* read new bytes */
            if (s < F - 1) text_buf[s + N] = c;  /* If the position is
                    near the end of buffer, extend the buffer to make
                    string comparison easier. */
            s = (s + 1) & (N - 1);  r = (r + 1) & (N - 1);
            /* Since this is a ring buffer, increment the position
               modulo N. */
            InsertNode(r);  /* Register the string in text_buf[r..r+F-1] */
        }
        while (i++ < last_match_length) {       /* After the end of text, */
            DeleteNode(s);                                  /* no need to read, but */
            s = (s + 1) & (N - 1);  r = (r + 1) & (N - 1);
            if (--len) InsertNode(r);               /* buffer may not be empty. */
        }
    } while (len > 0);      /* until length of string to be processed is zero */
    if (code_buf_ptr > 1) {         /* Send remaining code. */
        for (i = 0; i < code_buf_ptr; i++) putc(code_buf[i], dst_file);
        codesize += code_buf_ptr;
    }
    return codesize;
}

// simple and straight encoding scheme for Yaz0
uint32_t simpleEnc(uint8_t *src, uint32_t size, uint32_t pos, uint32_t *pMatchPos)
{
    uint32_t startPos = pos - 0x1000;
    uint32_t numBytes = 1;
    uint32_t matchPos = 0;
    uint32_t i;
    uint32_t j;

    if (pos < 0x1000)
        startPos = 0;
    for (i = startPos; i < pos; i++)
    {
        for (j = 0; j < size - pos; j++)
        {
            if (src[i + j] != src[j + pos])
                break;
        }
        if (j > numBytes)
        {
            numBytes = j;
            matchPos = i;
        }
    }
    *pMatchPos = matchPos;
    if (numBytes == 2)
        numBytes = 1;
    return numBytes;
}

// a lookahead encoding scheme for ngc Yaz0
uint32_t nintendoEnc(uint8_t* src, uint32_t size, uint32_t pos, uint32_t *pMatchPos)
{
    uint32_t numBytes = 1;
    static uint32_t numBytes1;
    static uint32_t matchPos;
    static int prevFlag = 0;

    // if prevFlag is set, it means that the previous position was determined by look-ahead try.
    // so just use it. this is not the best optimization, but nintendo's choice for speed.
    if (prevFlag == 1) {
        *pMatchPos = matchPos;
        prevFlag = 0;
        return numBytes1;
    }
    prevFlag = 0;
    numBytes = simpleEnc(src, size, pos, &matchPos);
    *pMatchPos = matchPos;

    // if this position is RLE encoded, then compare to copying 1 byte and next position(pos+1) encoding
    if (numBytes >= 3) {
        numBytes1 = simpleEnc(src, size, pos + 1, &matchPos);
        // if the next position encoding is +2 longer than current position, choose it.
        // this does not guarantee the best optimization, but fairly good optimization with speed.
        if (numBytes1 >= numBytes + 2) {
            numBytes = 1;
            prevFlag = 1;
        }
    }
    return numBytes;
}

struct Ret
{
    uint32_t srcPos, dstPos;
};

uint32_t CompressSlide(FILE *file_dst, FILE *src, uint32_t len)
{
    Ret r = { 0, 0 };
    uint8_t dst[96];    // 32 codes * 3 bytes maximum
    uint32_t dstSize = 4;

    uint32_t validBitCount = 0; //number of valid bits left in "code" byte
    uint32_t currCodeByte = 0;
    uint8_t *input = new uint8_t[len];
    fread(input, 1, len, src);
    WriteU32(file_dst, len);
    while (r.srcPos < len)
    {
        uint32_t numBytes;
        uint32_t matchPos;
        uint32_t srcPosBak;

        numBytes = nintendoEnc(input, len, r.srcPos, &matchPos);
        if (numBytes < 3)
        {
            //straight copy
            dst[r.dstPos] = input[r.srcPos];
            r.dstPos++;
            r.srcPos++;
            //set flag for straight copy
            currCodeByte |= (0x80000000 >> validBitCount);
        }
        else
        {
            //RLE part
            uint32_t dist = r.srcPos - matchPos - 1;
            uint8_t byte1, byte2, byte3;

            if (numBytes >= 0x12)  // 3 byte encoding
            {
                byte1 = 0 | (dist >> 8);
                byte2 = dist & 0xff;
                dst[r.dstPos++] = byte1;
                dst[r.dstPos++] = byte2;
                // maximum runlength for 3 byte encoding
                if (numBytes > 0xff + 0x12)
                    numBytes = 0xff + 0x12;
                byte3 = numBytes - 0x12;
                dst[r.dstPos++] = byte3;
            }
            else  // 2 byte encoding
            {
                byte1 = ((numBytes - 2) << 4) | (dist >> 8);
                byte2 = dist & 0xff;
                dst[r.dstPos++] = byte1;
                dst[r.dstPos++] = byte2;
            }
            r.srcPos += numBytes;
        }
        validBitCount++;
        //write 32 codes
        if (validBitCount == 32)
        {
            WriteU32(file_dst, currCodeByte);
            fwrite(dst, 1, r.dstPos, file_dst);
            dstSize += r.dstPos + 4;

            srcPosBak = r.srcPos;
            currCodeByte = 0;
            validBitCount = 0;
            r.dstPos = 0;
        }
    }
    if (validBitCount > 0)
    {
        WriteU32(file_dst, currCodeByte);
        fwrite(dst, 1, r.dstPos, file_dst);
        dstSize += r.dstPos + 4;

        currCodeByte = 0;
        validBitCount = 0;
        r.dstPos = 0;
    }
    delete[] input;
    return dstSize;
}

uint32_t CompressRle(FILE *file_dst, FILE *src, uint32_t len)
{
    uint32_t output_pos = 0;
    uint32_t input_pos = 0;
    uint32_t i;
    uint32_t copy_len = 0;
    uint8_t curr_byte;
    uint8_t next_byte;
    uint8_t *input = new uint8_t[len + 2]();
    fread(input, 1, len, src);
    while (input_pos < len) {
        curr_byte = input[input_pos];
        next_byte = input[input_pos + 1];
        if (curr_byte == next_byte) {
            copy_len = 0;
            for (i = 0; i < 127; i++) {
                curr_byte = input[input_pos + i];
                next_byte = input[input_pos + i + 1];
                if (curr_byte != next_byte || (input_pos + i) >= len) {
                    break;
                }
                copy_len++;
            }
            WriteU8(file_dst, copy_len);
            WriteU8(file_dst, input[input_pos]);
            output_pos += 2;
            input_pos += copy_len;
        }
        else {
            copy_len = 0;
            for (i = 0; i < 127; i++) {
                curr_byte = input[input_pos + i];
                next_byte = input[input_pos + i + 1];
                if (curr_byte == next_byte || (input_pos + i) >= len)
                {
                    break;
                }
                copy_len++;
            }
            WriteU8(file_dst, copy_len | 0x80);
            fwrite(&input[input_pos], 1, copy_len, file_dst);
            output_pos += copy_len+1;
            input_pos += copy_len;
        }
    }
    delete[] input;
    return output_pos;
}

#define DEFLATE_BUF_SIZE 16384

uint32_t CompressZlib(FILE *file_dst, FILE *src, uint32_t len)
{
    int ret;
    int flush;
    uint32_t have;
    uint32_t size_left = len;
    uint32_t input_offset = 0;
    uint32_t output_size = 0;
    z_stream strm;
    //static prevents Stack Analysis Warnings
    static uint8_t in[DEFLATE_BUF_SIZE];
    static uint8_t out[DEFLATE_BUF_SIZE];
    uint8_t *input = new uint8_t[len];
    fread(input, 1, len, src);
    strm.zalloc = Z_NULL;
    strm.zfree = Z_NULL;
    strm.opaque = Z_NULL;
    strm.avail_in = len;
    strm.next_in = (Bytef *)input;
    ret = deflateInit(&strm, Z_BEST_COMPRESSION);
    if (ret != Z_OK)
    {
        return 0;
    }
    WriteU32(file_dst, len);
    size_t comp_len_ofs = ftell(file_dst);
    WriteU32(file_dst, 0);
    flush = Z_NO_FLUSH;
    while (flush != Z_FINISH)
    {
        strm.avail_in = DEFLATE_BUF_SIZE;
        if (size_left < DEFLATE_BUF_SIZE)
        {
            strm.avail_in = size_left;
            flush = Z_FINISH;
        }
        memcpy(in, &input[input_offset], strm.avail_in);
        strm.next_in = in;
        do {
            strm.avail_out = DEFLATE_BUF_SIZE;
            strm.next_out = out;
            ret = deflate(&strm, flush);    /* no bad return value */
            have = DEFLATE_BUF_SIZE - strm.avail_out;
            fwrite(out, 1, have, file_dst);
            output_size += have;
        } while (strm.avail_out == 0);

        size_left -= DEFLATE_BUF_SIZE;
        input_offset += DEFLATE_BUF_SIZE;
    }
    size_t data_end_ofs = ftell(file_dst);
    fseek(file_dst, comp_len_ofs, SEEK_SET);
    WriteU32(file_dst, output_size);
    fseek(file_dst, data_end_ofs, SEEK_SET);
    (void)deflateEnd(&strm);
    return output_size+8;
}\

struct FileEntry {
    std::string id;
    std::string path;
    uint32_t comp_type;
};

std::vector<FileEntry> file_entry_list;

uint32_t GetCompTypeValue(std::string type)
{
    std::string type_table[4] = { "lzss", "slide", "rle", "zlib" };
    uint32_t type_values[4] = { 1, 4, 5, 7 };
    std::transform(type.begin(), type.end(), type.begin(), ::tolower);
    for (uint32_t i = 0; i < 4; i++) {
        if (type_table[i] == type) {
            return type_values[i];
        }
    }
    return 0;
}

int main(int argc, char **argv)
{
    ParseOptions(argc, argv);
    tinyxml2::XMLDocument document;
    PrintXmlError(document.LoadFile(xml_path.c_str()));
    tinyxml2::XMLElement *root = document.FirstChild()->ToElement();
    if (!root) {
        PrintXmlError(tinyxml2::XML_ERROR_FILE_READ_ERROR);
    }
    tinyxml2::XMLElement *file_element = root->FirstChildElement("file");
    std::string xml_dir = xml_path;
    if (xml_dir.find_last_of("\\/") != std::string::npos) {
        xml_dir = xml_dir.substr(0, xml_dir.find_last_of("\\/") + 1);
    } else {
        xml_dir = "\\";
    }
    while (file_element) {
        FileEntry entry;
        const char *str_temp;
        tinyxml2::XMLError error = file_element->QueryAttribute("id", &str_temp);
        if (error != tinyxml2::XML_SUCCESS && error != tinyxml2::XML_NO_ATTRIBUTE) {
            PrintXmlError(error);
        } else if(error != tinyxml2::XML_NO_ATTRIBUTE){
            entry.id = "file"+std::to_string(file_entry_list.size());
        } else {
            entry.id = str_temp;
        }
        PrintXmlError(file_element->QueryAttribute("path", &str_temp));
        std::string std_temp = str_temp;
        entry.path = xml_dir+std_temp;
        PrintXmlError(file_element->QueryAttribute("compress_type", &str_temp));
        entry.comp_type = GetCompTypeValue(str_temp);
        file_entry_list.push_back(entry);
        file_element = file_element->NextSiblingElement("file");
    }
    FILE *bin_file = fopen(bin_path.c_str(), "wb");
    if (!bin_file) {
        PrintError("Failed to Open %s for Writing.\n", bin_path.c_str());
    }
    uint32_t file_count = file_entry_list.size();
    uint32_t *ofs_table = new uint32_t[file_count]();
    WriteU32(bin_file, file_count);
    for (uint32_t i = 0; i < file_count; i++) {
        WriteU32(bin_file, ofs_table[i]);
    }
    uint32_t data_ofs = ftell(bin_file);
    for (uint32_t i = 0; i < file_count; i++) {
        ofs_table[i] = data_ofs;
        FILE *data_file = fopen(file_entry_list[i].path.c_str(), "rb");
        if (!data_file) {
            PrintError("Failed to Open %s for Reading.\n", file_entry_list[i].path.c_str());
        }
        fseek(data_file, 0, SEEK_END);
        uint32_t raw_size = ftell(data_file);
        fseek(data_file, 0, SEEK_SET);
        uint32_t comp_type = file_entry_list[i].comp_type;
        WriteU32(bin_file, raw_size);
        WriteU32(bin_file, comp_type);

        size_t comp_size = raw_size;
        switch (comp_type) {
            case 1:
                comp_size = CompressLzss(bin_file, data_file);
                break;

            case 4:
                comp_size = CompressSlide(bin_file, data_file, raw_size);
                break;

            case 5:
                comp_size = CompressRle(bin_file, data_file, raw_size);
                break;

            case 7:
                comp_size = CompressZlib(bin_file, data_file, raw_size);
                break;

            default:
                break;
        }
        fclose(data_file);
        data_ofs += comp_size + 8;
    }
    fseek(bin_file, 4, SEEK_SET);
    for (uint32_t i = 0; i < file_count; i++) {
        WriteU32(bin_file, ofs_table[i]);
    }
    delete[] ofs_table;
    fclose(bin_file);
    return 0;
}