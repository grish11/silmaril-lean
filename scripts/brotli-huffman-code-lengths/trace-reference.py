"""Trace read positions and secondary lengths on a temporary pinned decoder."""
import sys
from pathlib import Path


def insert(source, anchor, addition):
    if source.count(anchor) != 1:
        raise ValueError("unexpected difference in pinned reference sources")
    return source.replace(anchor, addition + anchor, 1)


def instrument(root):
    path = root / "c/dec/decode.c"
    source = "#include <stdio.h>\n" + path.read_text()
    source = insert(source, "        BROTLI_LOG_UINT(h->sub_loop_counter);", """
        fprintf(stderr, "selector %llu %llu %zu\\n",
                (unsigned long long)alphabet_size_max,
                (unsigned long long)h->sub_loop_counter,
                8 * BrotliBitReaderGetAvailIn(br) + BrotliGetAvailableBits(br));
""")
    source = insert(source, "        BrotliBuildCodeLengthsHuffmanTable(h->table,", """
        fprintf(stderr, "secondary %zu",
                8 * BrotliBitReaderGetAvailIn(br) + BrotliGetAvailableBits(br));
        for (i = 0; i < BROTLI_CODE_LENGTH_CODES; ++i) {
          fprintf(stderr, " %u", (unsigned)h->code_length_code_lengths[i]);
        }
        fputc('\\n', stderr);
""")
    path.write_text(source)


if __name__ == "__main__":
    instrument(Path(sys.argv[1]))
