module

public import Silmaril.Logic.Separation.Parameterized.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Separation.Parameterized

/-- Fresh argument values and the current resource vary together; ambient
object values remain fixed throughout this recursive predicate's LFP. -/
def bodyOperator {A : Signature} (M : Model A) {r k} {P' : Fin (r+1) → Nat}
    (body : Pattern A P' (P' 0 + k)) (η : RelEnv M (P' ∘ Fin.succ))
    (ρ : Tuple M k) : Set (State M (P' 0)) →o Set (State M (P' 0)) where
  toFun X := {s | (appendValues M s.1 ρ, s.2) ∈ body.denote M (insert M P' η X)}
  monotone' := fun _ _ h _ hs =>
    (body.denote M).monotone ((insert M P' η).monotone h) hs

def lfpSet {A : Signature} (M : Model A) {r k} {P' : Fin (r+1) → Nat}
    (body : Pattern A P' (P' 0 + k)) (η : RelEnv M (P' ∘ Fin.succ))
    (ρ : Tuple M k) : Set (State M (P' 0)) := (bodyOperator M body η ρ).lfp

theorem lfpSet_unfold {A : Signature} (M : Model A) {r k} {P' : Fin (r+1) → Nat}
    (body : Pattern A P' (P' 0 + k)) (η : RelEnv M (P' ∘ Fin.succ)) (ρ : Tuple M k) :
    lfpSet M body η ρ = bodyOperator M body η ρ (lfpSet M body η ρ) :=
  (bodyOperator M body η ρ).map_lfp.symm

theorem lfpSet_induction {A : Signature} (M : Model A) {r k} {P' : Fin (r+1) → Nat}
    (body : Pattern A P' (P' 0 + k)) (η : RelEnv M (P' ∘ Fin.succ)) (ρ : Tuple M k)
    (X : Set (State M (P' 0))) (closed : bodyOperator M body η ρ X ⊆ X) :
    lfpSet M body η ρ ⊆ X := (bodyOperator M body η ρ).lfp_le closed

theorem Pattern.denote_lfp {A : Signature} (M : Model A) {r k} {P' : Fin (r+1) → Nat}
    (body : Pattern A P' (P' 0 + k)) (args : Fin (P' 0) → Term A k)
    (η : RelEnv M (P' ∘ Fin.succ)) (ρ : Tuple M k) (h : M.resource.carrier) :
    (ρ,h) ∈ (Pattern.lfp body args).denote M η ↔
      ((fun j => (args j).eval M ρ), h) ∈ lfpSet M body η ρ := Iff.rfl

end Silmaril.Logic.Separation.Parameterized
