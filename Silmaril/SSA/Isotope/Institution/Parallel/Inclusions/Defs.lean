module

public import Silmaril.SSA.Isotope.Institution.Parallel.Thms

/-! Translations of exact equations along the native lower-tier embeddings. -/

@[expose] public section

namespace Silmaril.Isotope.Parallel.Institution.Equation

open Silmaril.Isotope.Institution

universe u v

variable {τ ε : Type u} {S : InstrSig τ ε} {ν : Type v} [DecidableEq ν] {Γ : Ctx ν τ}
  {n : Nat} {β : BoundCtx τ n} {A : τ}

/-- Translate a pair of exact LetSeq endpoints into the sequential-control parallel tier. -/
def ofLetSeq [HasProduct τ] [HasUnit τ] {l r : LetSeq.LocallyNameless.Tm ν S.Instr n}
    (dl : LetSeq.LocallyNameless.Derivation S.Instr Γ β l A)
    (dr : LetSeq.LocallyNameless.Derivation S.Instr Γ β r A) : Equation S .seq Γ :=
  ⟨n, β, A, LetPar.embed l, LetPar.embed r, LetPar.derivation dl, LetPar.derivation dr⟩

/-- Translate a pair of exact LetCase endpoints into the parallel case tier. -/
def ofLetCase [TypeFormers τ] {l r : LetCase.LocallyNameless.Tm ν S.Instr n}
    (dl : LetCase.LocallyNameless.Derivation S.Instr Γ β l A)
    (dr : LetCase.LocallyNameless.Derivation S.Instr Γ β r A) : Equation S .case Γ :=
  ⟨n, β, A, LetParCase.embed l, LetParCase.embed r, LetParCase.derivation dl, LetParCase.derivation dr⟩

/-- Widen both endpoints into the case tier, retaining all parallel constructors. -/
def ofLetPar [TypeFormers τ] (φ : Equation S .seq Γ) : Equation S .case Γ :=
  ⟨φ.n, φ.bound, φ.result, LetParCase.ofLetPar φ.left, LetParCase.ofLetPar φ.right,
    LetParCase.ofLetParDerivation φ.lhs, LetParCase.ofLetParDerivation φ.rhs⟩

end Silmaril.Isotope.Parallel.Institution.Equation
