"""Observe first-command literal positions and context selection in libbrotli."""
from pathlib import Path
import runpy
import sys

scripts = Path(__file__).resolve().parents[1]
runpy.run_path(str(scripts / "brotli-command/trace-reference.py"))
path = Path(sys.argv[1]) / "c/dec/decode.c"
source = path.read_text()

for anchor, snippet in (
    ("        PrepareLiteralDecoding(s);", r"""
        fprintf(stderr, "literal_header %u %u %u %u %d\n",
                (unsigned)s->num_block_types[0], (unsigned)s->num_block_types[1],
                (unsigned)s->num_literal_htrees, (unsigned)s->context_modes[0],
                s->meta_block_remaining_len);
"""),
    ("      context = BROTLI_CONTEXT(p1, p2, s->context_lookup);", r"""
      const uint8_t prior1 = p1;
      const uint8_t prior2 = p2;
      const size_t literal_begin =
          8 * BrotliBitReaderGetAvailIn(br) + BrotliGetAvailableBits(br);
"""),
    ("      s->ringbuffer[pos] = p1;", r"""
      fprintf(stderr, "literal %u %u %u %u %u %zu %zu\n",
              (unsigned)prior1, (unsigned)prior2, (unsigned)context,
              (unsigned)s->context_map_slice[context], (unsigned)p1,
              literal_begin,
              8 * BrotliBitReaderGetAvailIn(br) + BrotliGetAvailableBits(br));
"""),
    ("  BROTLI_LOG_UINT(s->meta_block_remaining_len);\n  if (BROTLI_PREDICT_FALSE", r"""
  fprintf(stderr, "literal_end %zu %d\n",
          8 * BrotliBitReaderGetAvailIn(br) + BrotliGetAvailableBits(br),
          s->meta_block_remaining_len);
"""),
):
    if source.count(anchor) != 1:
        raise ValueError(f"unexpected pinned native literal code at {anchor!r}")
    source = source.replace(anchor, snippet + anchor, 1)
path.write_text(source)
