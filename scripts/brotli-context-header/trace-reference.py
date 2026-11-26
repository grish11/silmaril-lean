"""Extend the native block-control trace to the context-map boundary."""
from pathlib import Path
import runpy
import sys

root = Path(sys.argv[1])
scripts = Path(__file__).resolve().parents[1]
runpy.run_path(str(scripts / "brotli-block-controls/trace-reference.py"))
path = root / "c/dec/decode.c"
source = path.read_text()
anchor = "        s->state = BROTLI_STATE_CONTEXT_MAP_1;"
if source.count(anchor) != 1:
    raise ValueError("unexpected pinned context-mode source")
source = source.replace(anchor, """
        {
          size_t i;
          BrotliBitReader* header = &s->br;
          fprintf(stderr, "context %u %u %zu",
                  s->distance_postfix_bits, s->num_direct_distance_codes,
                  8 * BrotliBitReaderGetAvailIn(header) + BrotliGetAvailableBits(header));
          for (i = 0; i < s->num_block_types[0]; ++i) {
            fprintf(stderr, " %u", (unsigned)s->context_modes[i]);
          }
          fputc('\\n', stderr);
        }
""" + anchor)
path.write_text(source)
