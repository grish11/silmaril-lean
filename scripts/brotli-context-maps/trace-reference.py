"""Trace the RFC context-map prefixes without changing libbrotli decoding."""
from pathlib import Path
import runpy
import sys

scripts = Path(__file__).resolve().parents[1]
runpy.run_path(str(scripts / "brotli-context-header/trace-reference.py"))
path = Path(sys.argv[1]) / "c/dec/decode.c"
source = path.read_text()
for anchor, snippet in (
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
    if source.count(anchor) != 1:
        raise ValueError("unexpected pinned context-map source")
    source = source.replace(anchor, snippet + anchor, 1)
path.write_text(source)
