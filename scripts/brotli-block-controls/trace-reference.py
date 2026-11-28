"""Trace compressed meta-block control boundaries in a temporary native checkout."""
from pathlib import Path
import sys

path = Path(sys.argv[1]) / "c/dec/decode.c"
source = "#include <stdio.h>\n" + path.read_text()
for anchor, label, value in (
    ("        /* Reads 1..11 bits. */", "start", "0"),
    ("        BROTLI_LOG_UINT(s->num_block_types[s->loop_counter]);", "types", "s->num_block_types[s->loop_counter]"),
    ("        BROTLI_LOG_UINT(s->block_length[s->loop_counter]);", "length", "s->block_length[s->loop_counter]"),
):
    if source.count(anchor) != 1:
        raise ValueError("unexpected pinned libbrotli source")
    source = source.replace(anchor, f"""
        fprintf(stderr, "{label} %d %llu %zu\\n",
                (int)s->loop_counter, (unsigned long long)({value}),
                8 * BrotliBitReaderGetAvailIn(br) + BrotliGetAvailableBits(br));
""" + anchor, 1)
path.write_text(source)
