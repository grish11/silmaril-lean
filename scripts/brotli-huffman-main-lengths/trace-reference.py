"""Trace the exact offsets and final code lengths on a temporary pinned decoder."""
from pathlib import Path
import runpy
import sys

root = Path(sys.argv[1])
prior = Path(__file__).resolve().parents[1] / "brotli-huffman-code-lengths/trace-reference.py"
base = runpy.run_path(str(prior))
base["instrument"](root)
path = root / "c/dec/decode.c"
source = path.read_text()
source = base["insert"](source, "        table_size = BrotliBuildHuffmanTable(", """
        {
          uint8_t depths[BROTLI_NUM_COMMAND_SYMBOLS] = {0};
          int len;
          size_t i;
          if (alphabet_size_limit > sizeof(depths)) abort();
          for (len = 1; len <= BROTLI_HUFFMAN_MAX_CODE_LENGTH; ++len) {
            int symbol = len - (BROTLI_HUFFMAN_MAX_CODE_LENGTH + 1);
            unsigned count = h->code_length_histo[len];
            while (count-- != 0) {
              symbol = h->symbol_lists[symbol];
              depths[symbol] = (uint8_t)len;
            }
          }
          fprintf(stderr, "main %zu",
                  8 * BrotliBitReaderGetAvailIn(br) + BrotliGetAvailableBits(br));
          for (i = 0; i < alphabet_size_limit; ++i) {
            fprintf(stderr, " %u", (unsigned)depths[i]);
          }
          fputc('\\n', stderr);
        }
""")
path.write_text(source)
