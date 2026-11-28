module

public import Silmaril.SSA.Isotope.LetSeq.StraightLine.Defs
public import Silmaril.SSA.Isotope.LetIter.Categorical.Kleisli.Thms
public import Silmaril.SSA.Isotope.LetCase.AbortSequence.Thms

public section

namespace Silmaril.Isotope.LetSeq.StraightLine

open LocallyNameless (Derivation Equiv HasType)
open Silmaril.Isotope.Semantics (BoundEnv InstructionModel)
open LetIter.Semantics.Categorical (denote_eq_of_abortEquiv_nil)

set_option backward.isDefEq.respectTransparency false

theorem replay_proof {n : Nat} {β : BoundCtx Types n} {t : Term n}
    (w : Admitted β t) : Equiv false Γ₀ β t w.normal Atom := by
  induction w with
  | ret i => exact .refl (slotDerivation i).toHasType
  | aliasReturn i => exact Equiv.letBeta .bv (slotDerivation i).toHasType .bv
  | request f x y rest ih => exact .let₂ (.refl (requestDerivation f x y).toHasType) ih
  | bound f x y rest ih =>
    have request := (requestDerivation f x y).toHasType
    exact (Equiv.bindPair request ih.hasType.1).symm.trans (.let₂ (.refl request) ih)

private theorem model_respectsPure : InstructionModel.RespectsPure (ε := Bool) model := by
  intro f h
  cases h

theorem case_sound_proof {n : Nat} {β : BoundCtx Types n} {A : Types}
    {t u : LetCase.LocallyNameless.Tm Empty Request n}
    (d : LetCase.LocallyNameless.Derivation Request Γ₀ β t A)
    (e : LetCase.LocallyNameless.Derivation Request Γ₀ β u A)
    (h : LetCase.LocallyNameless.Equiv false Γ₀ β t u A) (ρ : BoundEnv Value β) :
    d.denote Value model (fun x => x.elim) ρ = e.denote Value model (fun x => x.elim) ρ := by
  have abort : LetCase.LocallyNameless.AbortEquiv false Γ₀ β t u A := .equiv h
  have sound := denote_eq_of_abortEquiv_nil (fun _ : Unit => Nat) model model_respectsPure
    abort.toLetIter (Morphism.CaseIter.derivation d) (Morphism.CaseIter.derivation e) ρ
  simpa only [Morphism.CaseIter.denote_derivation] using sound

theorem seq_sound_proof {n : Nat} {β : BoundCtx Types n} {A : Types} {t u : Term n}
    (d : Derivation Request Γ₀ β t A) (e : Derivation Request Γ₀ β u A)
    (h : Equiv false Γ₀ β t u A) (ρ : BoundEnv Value β) :
    run d ρ = run e ρ := by
  simpa only [run, Morphism.SeqCase.denote_derivation] using
    case_sound_proof (Morphism.SeqCase.derivation d) (Morphism.SeqCase.derivation e)
      (Morphism.SeqCase.embed_equiv h) ρ

end Silmaril.Isotope.LetSeq.StraightLine
