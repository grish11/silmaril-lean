# Actual darkhttpd unsigned-byte log predicate

This is the unchanged static `needs_logencoding(const unsigned char c)` definition
from darkhttpd 1.17, paired with its existing x86-64 O0 ELF function at `0x503e`
(41 bytes). It is a new **unproved** C→ELF context, not complete server semantics,
a public exported API guarantee, or a semantic proof.

`projection.json` pins the exact original source span and the identical span in a
saved whole preprocessed translation unit. Current-host GCC matches the recorded
14.2.0-19 version and the O0/macro-affecting flags. `-MMD` (dependency output) was
omitted, and preprocessing-only `-E/-P` were added. `preprocessing.json` is the
actual measured command; `preprocessing-context.json` records these differences.
Historical image/header identity, historical compile replay and whole-TU frontend
adequacy are **not** established. No ELF was built or modified.

The actual frontend parses that unchanged closure and elaborates it with the
pinned Cerberus runtime from the public `cast-sign-extend` oracle. `typed-ail.sexp`,
`program.sexp` and `runtime.sexp` are actual outputs; no `fixRet`, replacement
body/callee or desired-refinement assumption is used. The body, parameter object,
unsigned-char type and signed-int result are selected only after successful
computed Core/procedure/ABI metadata lookup. Failed lookup has no default body.
The regression checks the saved functions/metadata against actual elaboration.

The source context allocates and initializes the actual one-byte parameter, then
marks it readonly. It admits every byte value, quantifies over real source safety
and machine first-return obligations, and requires all source memory fields except the interpreter diagnostic source
location to be preserved. Allocation, byte, pointer, lifetime and output state
are all observed; source-location updates are diagnostic rather than C effects. The machine signature has one `uint8` argument: only DIL
is constrained; upper register bits remain unspecified. The result uses EAX's
signed low32 bits. The O0 stack footprint is explicitly twelve bytes below entry
RSP, covering saved RBP and the one-byte spill at RSP-12. All other machine bytes
and mapping metadata must be preserved; callee-saved/return ABI obligations are
retained. There are no C procedure callees, globals, heap or I/O effects.

Kernel facts bind the actual source/TU spans, ELF code and static symbol identity.
A finite regression executes the actual Core on all256 byte arguments, checks the
result and memory, and rejects a missing allocation. ABI examples admit nonzero
upper register bits and reject a different low byte. These checks **do not prove**
the contextual obligation across arbitrary machine caller states. Zero corpus
semantic proofs are claimed.

Reproduce the input identity gate and regenerate actual frontend outputs:

```sh
python3 -I tools/corpus/check_darkhttpd_logencoding_inputs.py
lake env lean -DwarningAsError=true --run tools/corpus/DarkhttpdLogEncodingInputs.lean
lake build --wfail Silmaril.Elf.Corpus.DarkhttpdLogEncoding.Context.Defs
lake env lean -DwarningAsError=true --run tests/cerberus/DarkhttpdLogEncodingContext.lean
```

Regeneration writes the three committed frontend outputs; compare their hashes
against the manifest rather than silently accepting changed evidence. The
read-only corpus viewer keeps this source/Core context separate from binary
pairs and compiler fixtures. All corpus refinements remain UNPROVED, with842
artifact rows/707 hashes retained and ELF bytes outside the database.
