# Figure 18 completion for a structured while

Figure 18 shows why the return value alone can miss a strict computation.
The unchecked PEG returns `13` while leaving the discarded quotient
undemanded. The paper threads a non-termination token through effectful
operators, adds a token result to loop passes, and observes the final token
alongside the data result. [Figure 18 and §6.4](https://arxiv.org/pdf/1012.1802v3#page=39)

## Emitted PEG

`Structured.Token.translate` accepts a typed top-level while with a
loop-free body. `Body.ofStmt` accepts existing typed loop-free SIMPLE
syntax, and `Body.source_ofStmt` identifies its source semantics with
the original statement. The ordered roots
are the data result and a Boolean completion marker. The operations of the
original instruction set retain their interpretation, including partiality.
The additional operations have fixed interpretations:

- A nullary seed produces the initial marker.
- Each assignment emits a strict `after` operation with the incoming marker
  and the assignment value as operands. It returns the incoming marker when
  both operands are defined. A later projection can discard the value from
  the data store while the marker still depends on it.
- Sequence passes the new marker to the next statement. Projection forwards
  the marker directly.
- Both arms of a conditional start with the same input store and incoming
  marker. The compiler joins the marker and every live data slot with
  Figure 11 `φ` nodes using the same guard. A defined guard selects only the
  corresponding arm. An undefined guard leaves the joined marker bottom.
  A strict operation in the selected arm still contributes to its marker
  when its data result is discarded.

The compiler uses the existing structured loop builder and its checked
demand rank. A separate carried θ takes the seed at iteration zero and the
body marker from the previous iteration thereafter. The completion root
samples this θ at the same first pass as the returned data. A defined pass
requires the complete guard prefix; a defined completion eval requires the
marker through that first exit. At zero trips it needs the seed and the
initial guard, with no body step. This represents the paper's loop
completion output with an ordinary pass and a token eval for this fragment.
[Compiler](../../Silmaril/SSA/PEG/Simple/Structured/Completion/Token/Defs.lean)

## Correspondence

Under the compiler's Boolean negation law, any successful original SIMPLE
return defines both ordered PEG roots with the same returned data and a
`true` marker. A defined marker alone reconstructs a successful original
SIMPLE run and establishes the matching data result. The proof uses the
actual Figure 11 first pass and token samples to justify each complete
source step. It also uses the existing loop-free interpreter's
correspondence with `Exec`. The emitted PEG supplies the completion
evidence directly. [Theorems](../../Silmaril/SSA/PEG/Simple/Structured/Completion/Token/Thms.lean)

The straight-line #4615 countdown retains the same data result `0` and first
pass `2` on the failing input, with a bottom completion root. The conditional
countdown has one discarded probe in each arm. Both directions complete
when the selected probe is defined, even though a row in the untaken arm
is bottom. Swapping only the probe input makes the selected operation fail.
The data result still equals `0` and the completion root is bottom in both
directions. Zero-trip runs define both roots with either direction selected
by the input. [Regressions](../../tests/ssa/PEGSimple.lean)

Nested or discarded loops, arbitrary effect tokens, and the paper's
multi-result pass syntax are outside this slice. The observation
records successful completion. Bottom is shared by faults and divergence.
