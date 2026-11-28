"""Observe the header tables installed by pinned libbrotli."""
from pathlib import Path
import runpy
import sys

scripts = Path(__file__).resolve().parents[1]
runpy.run_path(str(scripts / "brotli-context-maps/trace-reference.py"))
path = Path(sys.argv[1]) / "c/dec/decode.c"
source = path.read_text()


def insert_before(anchor, code):
    global source
    if source.count(anchor) != 1:
        raise ValueError(f"unexpected pinned native header code at {anchor!r}")
    source = source.replace(anchor, code + anchor, 1)


insert_before("static BrotliDecoderErrorCode ReadHuffmanCode(", r"""
static void TraceHeaderCodes(const HuffmanCode* table,
                             brotli_reg_t alphabet,
                             BrotliDecoderState* s) {
  const char* group;
  unsigned ordinal = 0;
  switch (s->state) {
    case BROTLI_STATE_HUFFMAN_CODE_1: group = "type"; break;
    case BROTLI_STATE_HUFFMAN_CODE_2: group = "count"; break;
    case BROTLI_STATE_TREE_GROUP:
      group = "tree";
      ordinal = (unsigned)s->arena.header.htree_index;
      break;
    default: return;
  }
  fprintf(stderr, "codes %s %u %u %u %zu", group, (unsigned)s->loop_counter,
          ordinal, (unsigned)alphabet,
          8 * BrotliBitReaderGetAvailIn(&s->br) + BrotliGetAvailableBits(&s->br));
  for (unsigned bits = 0; bits < (1u << 15); ++bits) {
    BrotliBitReader scratch = {0};
    scratch.val_ = bits;
    scratch.bit_pos_ = 15;
    unsigned symbol = (unsigned)DecodeSymbol(bits, table, &scratch);
    unsigned width = 15u - (unsigned)BrotliGetAvailableBits(&scratch);
    if (symbol >= alphabet || width > 15) abort();
    if ((bits >> width) != 0) continue;
    unsigned code = 0;
    for (unsigned j = 0; j < width; ++j) {
      code = (code << 1) | ((bits >> j) & 1u);
    }
    fprintf(stderr, " %u %u %u", symbol, code, width);
  }
  fputc('\n', stderr);
}

""")
mark = """        h->substate_huffman = BROTLI_STATE_HUFFMAN_NONE;
        return BROTLI_DECODER_SUCCESS;"""
if source.count(mark) != 2:
    raise ValueError("unexpected successful native Huffman code paths")
source = source.replace(mark, "        TraceHeaderCodes(table, alphabet_size_limit, s);\n" + mark)
insert_before("        PrepareLiteralDecoding(s);", r"""        fprintf(stderr, "payload %zu\n",
                8 * BrotliBitReaderGetAvailIn(br) + BrotliGetAvailableBits(br));
""")
path.write_text(source)
