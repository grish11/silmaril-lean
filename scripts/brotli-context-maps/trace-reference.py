"""Trace the RFC context maps without changing libbrotli decoding."""
from pathlib import Path
import runpy
import sys

scripts = Path(__file__).resolve().parents[1]
runpy.run_path(str(scripts / "brotli-context-header/trace-reference.py"))
path = Path(sys.argv[1]) / "c/dec/decode.c"
source = path.read_text()
for anchor, snippet in (
    ("/* Decodes a context map.", """
static void TraceContextMap(const uint8_t* values, brotli_reg_t size,
                           int flag, BrotliBitReader* br) {
  fprintf(stderr, "map %d %zu ", flag,
          8 * BrotliBitReaderGetAvailIn(br) + BrotliGetAvailableBits(br));
  for (brotli_reg_t i = 0; i < size; ++i) {
    fprintf(stderr, "%02x", (unsigned)values[i]);
  }
  fprintf(stderr, "\\n");
}

"""),
    ("        memset(*context_map_arg, 0, (size_t)context_map_size);", """
        TraceContextMap(*context_map_arg, context_map_size, -1, br);
"""),
    ("          BROTLI_LOG_UINT(code);", """
          fprintf(stderr, "token %u\\n", (unsigned)code);
"""),
    ("      h->substate_context_map = BROTLI_STATE_CONTEXT_MAP_NONE;", """
      TraceContextMap(*context_map_arg, context_map_size, (int)bits, br);
"""),
    ("      result = DecodeVarLenUint8(s, br, num_htrees);", """
      fprintf(stderr, "begin %s %u %zu\\n",
              s->state == BROTLI_STATE_CONTEXT_MAP_1 ? "literal" : "distance",
              (unsigned)context_map_size,
              8 * BrotliBitReaderGetAvailIn(br) + BrotliGetAvailableBits(br));
"""),
    ("      BROTLI_LOG_UINT(*num_htrees);", """
      fprintf(stderr, "trees %u %zu\\n",
              (unsigned)*num_htrees,
              8 * BrotliBitReaderGetAvailIn(br) + BrotliGetAvailableBits(br));
"""),
    ("      BROTLI_LOG_UINT(h->max_run_length_prefix);", """
      fprintf(stderr, "rle %u\\n", (unsigned)h->max_run_length_prefix);
"""),
    ("      h->substate_context_map = BROTLI_STATE_CONTEXT_MAP_DECODE;", """
      fprintf(stderr, "symbols %zu\\n",
              8 * BrotliBitReaderGetAvailIn(br) + BrotliGetAvailableBits(br));
"""),
):
    line = "\n" + anchor
    if source.count(line) != 1:
        raise ValueError(f"unexpected pinned context-map source at {anchor!r}")
    if anchor.lstrip().startswith("memset"):
        source = source.replace(line, line + snippet.rstrip(), 1)
    else:
        source = source.replace(line, snippet + anchor, 1)
path.write_text(source)
