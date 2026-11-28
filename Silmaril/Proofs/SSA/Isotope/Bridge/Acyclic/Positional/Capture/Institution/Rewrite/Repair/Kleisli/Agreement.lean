module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Kleisli.Defs

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli

open CategoryTheory Silmaril.Elgot
open Isotope.Semantics (BoundEnv InstructionModel)
open Isotope.LetCase.LocallyNameless (AbortEquiv Derivation Tm)
open LetIter.Semantics.Categorical (boundEnv boundObj denoteOfType denoteOfType_eq denoteOfType_eq_of_abortEquiv)
open Morphism.CaseIter (derivation denote_derivation)

set_option backward.isDefEq.respectTransparency false

local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty Empty))

variable {m : Type → Type} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  {P : InstrSig (Ty Empty) Bool} (M : InstructionModel value P.Instr m)

private theorem embed_denote {n : Nat} {β : BoundCtx (Ty Empty) n}
    {t : Tm Empty P.Instr n} {A : Ty Empty} (h : Derivation P.Instr Γ₀ β t A) :
    letI := instructions M
    Isotope.LetCase.Semantics.Categorical.denote (J (m := m)) types h =
      denoteOfType value M (derivation h) := by
  let _ := instructions M
  induction h with
  | fv hi => cases hi
  | bv | unit => rfl
  | op _ ih | inl _ ih | inr _ ih | abort _ ih =>
    simp only [derivation, Isotope.LetCase.Semantics.Categorical.denote,
      denoteOfType, LetIter.Semantics.Categorical.denote] at ih ⊢
    rw [ih]
  | let₁ _ _ ih₁ ih₂ | let₂ _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ =>
    simp only [derivation, Isotope.LetCase.Semantics.Categorical.denote,
      denoteOfType, LetIter.Semantics.Categorical.denote] at ih₁ ih₂ ⊢
    rw [ih₁, ih₂]
  | case _ _ _ ih₁ ih₂ ih₃ =>
    simp only [derivation, Isotope.LetCase.Semantics.Categorical.denote,
      denoteOfType, LetIter.Semantics.Categorical.denote] at ih₁ ih₂ ih₃ ⊢
    rw [ih₁, ih₂, ih₃]

private theorem sat_iff_embedDenote (e : GrammarEquation P) :
    ((LetCase.inst Γ₀).obj P).Sat (algebra M) (grammarCase e) ↔
      denoteOfType value M (derivation (grammarCase e).2.1.2) =
        denoteOfType value M (derivation (grammarCase e).2.2.2) := by
  let d := (grammarCase e).2.1.2
  let d' := (grammarCase e).2.2.2
  refine (LetCase.sat_iff Γ₀ P (algebra M) d d').trans ?_
  let _ := instructions M
  change Isotope.LetCase.LocallyNameless.Models.denote
      (freydCaseAlgebra (J (m := m)) types (instructions M)) d =
    Isotope.LetCase.LocallyNameless.Models.denote
      (freydCaseAlgebra (J (m := m)) types (instructions M)) d' ↔ _
  rw [freydCaseAlgebra_denote, freydCaseAlgebra_denote, embed_denote, embed_denote]

theorem run_eq_of_sat_proof (e : GrammarEquation P)
    (sat : ((LetCase.inst Γ₀).obj P).Sat (algebra M) (grammarCase e))
    (ρ : boundObj types e.1.bound) :
    run M (grammarCase e).2.1.2 (boundEnv value ρ) =
      run M (grammarCase e).2.2.2 (boundEnv value ρ) := by
  have eq := (sat_iff_embedDenote M e).mp sat
  have obs := congrArg (fun f => f.of (PUnit.unit, ρ)) eq
  have free : LetIter.Semantics.Categorical.freeEnv value (Γ := Γ₀) PUnit.unit = noFree := by
    funext x
    exact x.elim
  simp only [denoteOfType_eq, denote_derivation, free] at obs
  exact obs

theorem sat_of_repaired_proof (pureM : InstructionModel.RespectsPure (ε := Bool) M)
    (e : GrammarEquation P) (h : Repaired false e) :
    ((LetCase.inst Γ₀).obj P).Sat (algebra M) (grammarCase e) :=
  (sat_iff_embedDenote M e).mpr
    (denoteOfType_eq_of_abortEquiv (Empty.elim : Empty → Type) M pureM (AbortEquiv.toLetIter h) _ _)

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli
