module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Defs
public import Silmaril.SSA.Isotope.LetCase.AbortSequence.Thms

/-! # Empty-sequencing proofs for witnessed LetCase equations -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite

open Isotope.LetCase.LocallyNameless (AbortCongr AbortEquiv)
open LambdaSSA.Region (packedExitType)

variable {τ ε : Type} [TypeFormers τ] {P : InstrSig τ ε}

/-- Native derivability with the opt-in typed empty-sequencing equations. -/
def Repaired (pe : ε) (e : GrammarEquation P) : Prop :=
  AbortEquiv pe (Ctx.nil : Ctx Empty τ) e.1.bound
    (grammarCase e).2.1.1 (grammarCase e).2.2.1 (packedExitType e.1.exits)

/-- The new rule under exact LetCase constructors on the witnessed terms. -/
def SequencesEmpty (e : GrammarEquation P) : Prop :=
  AbortCongr (Ctx.nil : Ctx Empty τ) (grammarCase e).2.1.2 (grammarCase e).2.2.2

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite
