# Cambridge UTF-8 S-expression documents

`AstCodec.SExpBytes.codec` composes a Cambridge structural codec with the
verified dotted S-expression reader and printer. It uses the original
constructor trees, including their tags, field order, and version
envelopes. The same adapter serves program terms and types, step
specifications, and finite may-return specifications.
[AST codecs](cambridge-ast-codecs.md) · [Step specifications](cambridge-step-specification.md) ·
[May-return specifications](cambridge-return-specification.md)

```lean
import Silmaril.Courses.Cambridge.AstCodec.SExpBytes
import Silmaril.Courses.Cambridge.L1.Codec
import Silmaril.Courses.Cambridge.ReturnSpecification.Format

open Silmaril.Courses.Cambridge

def l1SExpBytes := AstCodec.SExpBytes.codec L1.Codec.termSExp

def returnSExpBytes (context : StepSpecification.Context) :=
  AstCodec.SExpBytes.codec (ReturnSpecification.sexp context)
```

## Canonical output and external input

The encoder writes proper lists with parentheses, one ASCII space between
siblings, and every atom in double quotes. Inside a string it escapes
double quote, backslash, newline, carriage return, and tab. Other
characters are emitted literally in UTF-8, including non-ASCII Unicode
and controls such as NUL.

The decoder reads one complete UTF-8 datum. External text can use ASCII
space, tab, LF, CR and form feed, plus semicolon line comments. It also
accepts bare symbols, bar-quoted symbols, and double-quoted strings.
All three supply the same literal string atom to the structural codec.
The escapes in quoted tokens are `\\`, `\"`, `\|`, `\n`, `\r`, and
`\t`. Bare symbols use the library's maximal-token rule, with a lone
dot reserved for a list tail. Dotted notation is accepted when it yields
a proper list. Each nested list must end in the empty list. The selected
schema then checks the tags, arities, version, and any relevant bounds.
[External grammar and its Lean characterization](../../Silmaril/Formats/SExp/Dotted/Thms.lean)

For example, this external term uses a comment, bare atoms, and a
bar-quoted name containing a parenthesis and a semicolon.

```text
; an L1 term
(cambridge-ast-v1 L1 term (deref |猫😀 ();|))
```

Ill-formed UTF-8, misplaced dots, improper lists, unknown escapes,
unterminated quotes, and extra data after the datum are rejected.
Re-encoding a decoded external document picks the canonical spelling.
Whitespace, comments, and atom quoting choices are discarded.

## Checked contracts

`decode_encode` recovers the original program AST or typed sentence from
the actual emitted bytes. `reencode_canonical` recovers the exact byte
string on the canonical image. `text_of_encode` identifies the printed
string obtained by decoding those bytes as UTF-8. `decode_iff` separates
the complete text read, the proper-tree conversion, and structural schema
validation. Satisfaction of a decoded specification uses the existing
step or may-return institution.
[Lean bridge](../../Silmaril/Courses/Cambridge/AstCodec/SExpBytes.lean)

```sh
lake build --wfail +Silmaril.Courses.Cambridge.AstCodec.SExpBytes.Examples
```
