"""Read canonical assignments from the native decoder's installed tables."""
from pathlib import Path
import runpy
import sys

root = Path(sys.argv[1])
scripts = Path(__file__).resolve().parents[1]
runpy.run_path(str(scripts / "brotli-huffman-main-lengths/trace-reference.py"))
path = root / "c/dec/decode.c"
source = path.read_text()
build_end = "            table, HUFFMAN_TABLE_BITS, h->symbol_lists, h->code_length_histo);"
if source.count(build_end) != 1:
    raise ValueError("unexpected difference in pinned reference sources")
source = source.replace(build_end, build_end + """
        {
          unsigned codes[BROTLI_NUM_COMMAND_SYMBOLS] = {0};
          unsigned widths[BROTLI_NUM_COMMAND_SYMBOLS] = {0};
          unsigned low, sidx;
          if (alphabet_size_limit > BROTLI_NUM_COMMAND_SYMBOLS) abort();
          for (low = 0; low < (1u << 15); ++low) {
            BrotliBitReader scratch = {0};
            unsigned symbol, width, code = 0, j;
            scratch.val_ = low;
            scratch.bit_pos_ = 15;
            symbol = (unsigned)DecodeSymbol(low, table, &scratch);
            width = 15u - (unsigned)BrotliGetAvailableBits(&scratch);
            if (width == 0 || width > 15 || symbol >= alphabet_size_limit) abort();
            /* A code padded with zeros has one representative in this scan. */
            if ((low >> width) != 0) continue;
            if (widths[symbol] != 0) abort();
            for (j = 0; j < width; ++j) code = (code << 1) | ((low >> j) & 1u);
            codes[symbol] = code;
            widths[symbol] = width;
          }
          fprintf(stderr, "codes");
          for (sidx = 0; sidx < alphabet_size_limit; ++sidx) {
            fprintf(stderr, " %u %u", codes[sidx], widths[sidx]);
          }
          fputc('\\n', stderr);
        }
""", 1)
path.write_text(source)
