module

public import Silmaril.Calculi.LambdaCube.Semantics
public import Silmaril.Logic.Consequence.Institution.Defs

/-!
# Lambda-cube judgements as consequence systems

The dependent corners of the lambda cube (`Corner.lambdaP`, …, `Corner.cc`) are the library's
dependent type theories; there is no separate Martin-Löf type theory here. Their institution
(`Semantics.room`) has **judgements** as sentences: `Γ ⊢ t : A` and `Γ ⊢ t ≡ u : A`
(`PTSJudgment`), each carrying its own dependent context `Γ`, a telescope in which later types
may mention earlier variables. The consequence systems below therefore relate **lists of whole
judgements** to a judgement; they never split a context `Γ` into independent premises, and they
never read a list of types as a conjunction.

* `derivableSys c : System (List PTSJudgment) PTSJudgment`: `Js ⊢ j` iff `j` is derivable at the
  corner `c`. Derivability takes no judgement premises, so the premises are ignored: this is
  theoremhood, not hypothetical derivability.
* `Semantics.seq M := roomSeq M.room`: semantic consequence in the supplied semantics `M`:
  every model satisfying every judgement of `Js` satisfies `j`.
* `SemanticInclusion.seqTranslation f`: a semantic inclusion of corners translates `seq`
  (`corridorSeq` of its corridor; judgements are unchanged).

There is deliberately **no Gentzen (multiple-conclusion) instance**: a disjunction of
judgements is not a judgement form of these type theories, and the generic model-wise
`roomMulti M.room` exists but is not a sequent calculus of the cube. The classical,
point-wise LK reading is specific to HOL (`Silmaril.Logic.Consequence.HOL`).
-/

@[expose] public section

namespace Silmaril.Calculi.LambdaCube

open Silmaril.Consequence

/-- **Theoremhood at a corner**: `Js ⊢ j` iff `j` is derivable at `c` (premises ignored). -/
def derivableSys (c : Corner) : System (List PTSJudgment) PTSJudgment :=
  fun _ j => j.Derivable c

/-- **Semantic consequence of judgements** in the supplied semantics. -/
def Semantics.seq {c : Corner} (M : Semantics c) : System (List PTSJudgment) PTSJudgment :=
  roomSeq M.room

/-- A semantic inclusion of corners translates semantic consequence. -/
def SemanticInclusion.seqTranslation {c d : Corner} {h : c ≤ d} {M : Semantics c}
    {N : Semantics d} (f : SemanticInclusion h M N) : Translation M.seq N.seq :=
  corridorSeq f.corridor

end Silmaril.Calculi.LambdaCube
