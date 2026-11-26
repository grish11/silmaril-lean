module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Defs
import Silmaril.SSA.Isotope.LetIter.Categorical.Empty.Thms
import Silmaril.SSA.Isotope.Institution.Ordered.Thms

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite

open Isotope.LetCase.LocallyNameless (Equiv HasType Tm)
open LambdaSSA.Acyclic (Operand)
open LambdaSSA.Region (packedExitType)

set_option backward.isDefEq.respectTransparency false

variable {τ Φ ε : Type} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] {pe : ε}
  {n : Nat} {β : BoundCtx τ n}

local notation "U" => (unit : τ)
local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)

private def decodeHead (Φ : Type) (n : Nat) : Tm Empty Φ (n + 1) :=
  .case (.bv 0) (.bv 0) .unit

private theorem decodeHead_type (L : List τ) :
    HasType Φ Γ₀ (β.snoc (packedExitType (U :: L))) (decodeHead Φ n) U :=
  .case .bv .bv .unit

private theorem decoded_returnUnit (L : List τ) (a : Operand Φ β U) :
    Equiv pe Γ₀ β (.let₁ (returnUnit L a).toLetCase.1 (decodeHead Φ n)) a.1 U := by
  let K := packedExitType L
  let pack := packedExitType (U :: L)
  have tag : HasType Φ Γ₀ (β.snoc U) (.inl (.bv 0)) pack := .inl .bv
  have body : Equiv pe Γ₀ (β.snoc U) (.let₁ (.bv 0) (.inl (.bv 0))) (.inl (.bv 0)) pack :=
    let newest : HasType Φ Γ₀ (β.snoc U) (.bv 0) U := .bv
    let tag' : HasType Φ Γ₀ ((β.snoc U).snoc U) (.inl (.bv 0)) pack := .inl .bv
    Equiv.letBeta .bv newest tag'
  have head : Equiv pe Γ₀ β (returnUnit L a).toLetCase.1 (.let₁ a.1 (.inl (.bv 0))) pack :=
    .let₁ (.refl a.2.toHasType) body
  refine (Equiv.let₁ head (.refl (decodeHead_type L))).trans ?_
  refine (Equiv.bindLet a.2.toHasType tag (decodeHead_type L)).trans ?_
  have beta :
      Equiv pe Γ₀ (β.snoc U) (.let₁ (.inl (.bv 0)) (decodeHead Φ n).underBinder)
        (.case (.inl (.bv 0)) (.bv 0) .unit) U :=
    Equiv.letBeta (.inl .bv) tag (decodeHead_type L).underBinder
  have caseBeta :
      Equiv pe Γ₀ (β.snoc U) (.case (.inl (.bv 0)) (.bv 0) .unit)
        (.let₁ (.bv 0) (.bv 0)) U :=
    Equiv.caseBetaL .bv .bv (show HasType Φ Γ₀ ((β.snoc U).snoc K) .unit U from .unit)
  exact (Equiv.let₁ (.refl a.2.toHasType)
    (beta.trans (caseBeta.trans (Equiv.letEta (.bv (ι := 0)))))).trans
      (Equiv.letEta a.2.toHasType)

theorem reflect_returnUnit (L : List τ) (a b : Operand Φ β U)
    (h : Equiv pe Γ₀ β (returnUnit L a).toLetCase.1 (returnUnit L b).toLetCase.1
      (packedExitType (U :: L))) : Equiv pe Γ₀ β a.1 b.1 U :=
  (decoded_returnUnit L a).symm.trans
    ((Equiv.let₁ h (.refl (decodeHead_type L))).trans (decoded_returnUnit L b))

open Silmaril.Logic.Metatheory.TheoryModel (quotient quotientMap quotientMap_eq_iff)

theorem syntactic_sat_iff_proof {P : InstrSig τ ε} (pe : ε) (e : GrammarEquation P) :
    ((LetCase.inst Γ₀).obj P).Sat
      (Isotope.LetCase.LocallyNameless.Models.syntacticModel (Φ := P.Instr) pe Γ₀).algebra
      (grammarCase e) ↔ Derivable pe e := by
  let I := Isotope.LetCase.LocallyNameless.Models.syntaxIsInitial P.Instr Γ₀
  let E := Isotope.LetCase.LocallyNameless.Models.equationCongruence (Φ := P.Instr) pe Γ₀
  have h := I.hom_ext (I.to (quotient E)) (quotientMap E)
  let a := (grammarCase e).2.1
  let b := (grammarCase e).2.2
  change (I.to (quotient E)).map a = (I.to (quotient E)).map b ↔ E.Rel a b
  rw [h]
  exact quotientMap_eq_iff E a b

namespace EmptySequencing

theorem unprovable_proof (tail : List (Ty Empty)) : ¬ Derivable false (equation tail) := by
  intro h
  have native := reflect_returnUnit tail direct sequenced h
  exact LetIter.Semantics.Categorical.AbortCounterexample.exact_abortSequence_unprovable
    (Morphism.CaseIter.embed_equiv native)

end EmptySequencing
end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite
