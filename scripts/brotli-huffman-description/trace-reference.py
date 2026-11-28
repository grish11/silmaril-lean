"""Trace simple descriptions and installed codes in a pinned native decoder."""
from pathlib import Path
import runpy
import sys

root = Path(sys.argv[1])
scripts = Path(__file__).resolve().parents[1]
runpy.run_path(str(scripts / "brotli-huffman-main-table/trace-reference.py"))
insert = runpy.run_path(str(scripts / "brotli-huffman-code-lengths/trace-reference.py"))["insert"]
path = root / "c/dec/decode.c"
source = path.read_text()
source = insert(source, "        table_size = BrotliBuildSimpleHuffmanTable(table, HUFFMAN_TABLE_BITS,", """
        {
          size_t j;
          size_t count = h->symbol < 4 ? h->symbol + 1 : 4;
          fprintf(stderr, "simple %llu %zu",
                  (unsigned long long)h->symbol,
                  8 * BrotliBitReaderGetAvailIn(br) + BrotliGetAvailableBits(br));
          for (j = 0; j < count; ++j) {
            fprintf(stderr, " %u", (unsigned)h->symbols_lists_array[j]);
          }
          fputc('\\n', stderr);
        }
""")
anchor = "                                                   (uint32_t)h->symbol);"
if source.count(anchor) != 1:
    raise ValueError("unexpected difference in pinned simple builder")
source = source.replace(anchor, anchor + """
        {
          unsigned bits;
          fprintf(stderr, "simpleCodes");
          for (bits = 0; bits < 8; ++bits) {
            BrotliBitReader scratch = {0};
            unsigned symbol, width, code = 0, j;
            scratch.val_ = bits;
            scratch.bit_pos_ = 15;
            symbol = (unsigned)DecodeSymbol(bits, table, &scratch);
            width = 15u - (unsigned)BrotliGetAvailableBits(&scratch);
            if (symbol >= alphabet_size_limit || width > 3) abort();
            if ((bits >> width) != 0) continue;
            for (j = 0; j < width; ++j) code = (code << 1) | ((bits >> j) & 1u);
            fprintf(stderr, " %u %u %u", symbol, code, width);
          }
          fputc('\\n', stderr);
        }
""", 1)
path.write_text(source)
