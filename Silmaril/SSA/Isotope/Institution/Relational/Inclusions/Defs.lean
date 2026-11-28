module

public import Silmaril.SSA.Isotope.Institution.Relational.LetSeq.Thms
public import Silmaril.SSA.Isotope.Institution.Relational.LetCase.Thms
public import Silmaril.SSA.Isotope.Institution.Relational.LetIter.Thms
public import Silmaril.Raw.SSA.Isotope.Institution.Inclusions

/-! # Sentence inclusions for the exact sequential relational institutions -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Relational

open CategoryTheory Semantics Silmaril.Logic.Institution

universe u v

variable {τ ε ν : Type u} [DecidableEq ν] [TypeFormers τ]
variable {Γ : Ctx ν τ} {P : InstrSig τ ε}

/-- Include the selected LetSeq derivations using the existing exact sentence map. -/
abbrev seqCaseSentence (e : LetSeq.Sentence P Γ) : LetCase.Sentence P Γ :=
  ((Silmaril.Isotope.Institution.seqCaseRho (ε := ε) Γ).app P).sen e

/-- Include the selected LetCase derivations using the existing exact sentence map. -/
abbrev caseIterSentence (e : LetCase.Sentence P Γ) : LetIter.Sentence P Γ :=
  ((Silmaril.Isotope.Institution.caseIterRho (ε := ε) Γ).app P).sen e

variable (D : τ → Type v) (Γ) [ProductModel D] [UnitModel D] [CoproductModel D]

abbrev seqInst : Inst := ⟨InstrSig τ ε, LetSeq.institution D Γ⟩
abbrev caseInst : Inst := ⟨InstrSig τ ε, LetCase.institution D Γ⟩
abbrev iterInst : Inst := ⟨InstrSig τ ε, LetIter.institution D Γ⟩

end Silmaril.Isotope.Institution.Relational
