module

public import Silmaril.Logic.Consequence.HOL.Defs

/-! Proofs for `Silmaril.Logic.Consequence.HOL.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Logic.Consequence.HOL

open Silmaril.Consequence Silmaril.Consequence.HOL Silmaril.Logic.HOLLight
open Silmaril.Logic.Institution.Metatheory (HolSig)

universe u

variable {S : HolSig}

theorem seq_iff_entails (Γ : List (HOLProp S)) (p : HOLProp S) :
    seq.{u} S Γ p ↔ ∀ M : Model.{u} S.sig, Entails M (Γ.map Subtype.val).toFinset p.1 := by
  constructor
  · intro h M ρ ν hH
    exact h ⟨M, ρ, ν⟩ fun q hq => hH q.1 (List.mem_toFinset.2 (List.mem_map_of_mem hq))
  · intro h x hx
    refine h x.1 x.2.1 x.2.2 fun q hq => ?_
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hq)
    exact hx r hr

theorem globalSeq_iff_roomSeq (Γ : List (HOLProp S)) (p : HOLProp S) :
    globalSeq.{u} S Γ p ↔
      roomSeq (Silmaril.Logic.Institution.Metatheory.HOL.room.{u} S) (Γ.map closedSen)
        (closedSen p) := by
  have key : ∀ (M : Model.{u} S.sig) (q : HOLProp S),
      validIn satAt M q ↔ Entails M (closedSen q).hyps (closedSen q).concl :=
    fun M q => ⟨fun h ρ ν _ => h ⟨ρ, ν⟩,
      fun h x => h x.1 x.2 fun _ hm => absurd hm (Finset.notMem_empty _)⟩
  constructor
  · intro h M hM
    exact (key M.as p).1 (h M.as fun q hq => (key M.as q).2 (hM _ (List.mem_map_of_mem hq)))
  · intro h M hM
    refine (key M p).2 (h ⟨M⟩ fun s hs => ?_)
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hs
    exact (key M q).1 (hM q hq)

/-- The assignment `μ` that a type-respecting substitution denotes at `(ρ, ν)`. -/
noncomputable def substEnv (M : Model.{u} S.sig) (ρ : TypeValuation.{u}) (ν : FreeEnv M ρ)
    (σ : Nat → Ty → Tm) (hσ : ∀ n B, B.WellFormed S.sig.tyOps → HasType S.sig [] (σ n B) B) :
    FreeEnv M ρ := fun n B =>
  haveI := Classical.propDecidable (B.WellFormed S.sig.tyOps)
  if hB : B.WellFormed S.sig.tyOps then ((hσ n B hB).eval_exists M ρ ν BoundEnv.empty).choose
  else ν n B

theorem eval_substEnv (M : Model.{u} S.sig) (ρ : TypeValuation.{u}) (ν : FreeEnv M ρ)
    (σ : Nat → Ty → Tm) (hσ : ∀ n B, B.WellFormed S.sig.tyOps → HasType S.sig [] (σ n B) B)
    (n : Nat) (B : Ty) (hB : B.WellFormed S.sig.tyOps) :
    Eval M ρ ν BoundEnv.empty (σ n B) B (substEnv M ρ ν σ hσ n B) := by
  simp only [substEnv, hB, dite_true]
  exact ((hσ n B hB).eval_exists M ρ ν BoundEnv.empty).choose_spec

end Silmaril.Proofs.Logic.Consequence.HOL
