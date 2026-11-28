"""Observe successful insert-and-copy length reads in pinned libbrotli."""
from pathlib import Path
import runpy
import sys

scripts = Path(__file__).resolve().parents[1]
runpy.run_path(str(scripts / "brotli-block-controls/trace-reference.py"))
path = Path(sys.argv[1]) / "c/dec/decode.c"
source = path.read_text()

for anchor, snippet in (
    ("  CmdLutElement v;", r"""
  const size_t command_begin =
      8 * BrotliBitReaderGetAvailIn(br) + BrotliGetAvailableBits(br);
"""),
    ("  *insert_length += (int)insert_len_extra;", r"""
  fprintf(stderr, "command %u %u %u %u %u %zu %zu\n",
          (unsigned)s->block_type_rb[3], (unsigned)cmd_code,
          (unsigned)(v.insert_len_offset + insert_len_extra),
          (unsigned)s->copy_length, (unsigned)(v.distance_code != 0),
          command_begin,
          8 * BrotliBitReaderGetAvailIn(br) + BrotliGetAvailableBits(br));
"""),
    ("        PrepareLiteralDecoding(s);", r"""
        fprintf(stderr, "payload %zu\n",
                8 * BrotliBitReaderGetAvailIn(br) + BrotliGetAvailableBits(br));
"""),
):
    if source.count(anchor) != 1:
        raise ValueError(f"unexpected pinned command decoder at {anchor!r}")
    source = source.replace(anchor, snippet + anchor, 1)
path.write_text(source)
