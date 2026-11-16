module

public import Silmaril.Logic.Consequence.HOL.Defs
public import Silmaril.Logic.HOLLight.Soundness.Thms
public import Silmaril.Logic.HOLLight.Semantics.Logic

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

theorem holds_iff_of_eval {M : Model.{u} S.sig} {ρ : TypeValuation.{u}} {ν : FreeEnv M ρ} {t : Tm}
    {v : Value M ρ .bool} (hv : Eval M ρ ν BoundEnv.empty t .bool v) :
    Holds M ρ ν t ↔ Carrier.Truth v :=
  ⟨fun ⟨_, hw, ht⟩ => hw.unique hv ▸ ht, fun h => ⟨v, hv, h⟩⟩

theorem holds_disj {M : Model.{u} S.sig} {ρ : TypeValuation.{u}} {ν : FreeEnv M ρ}
    (p q : HOLProp S) :
    Holds M ρ ν (HOLProp.disj p q).1 ↔ Holds M ρ ν p.1 ∨ Holds M ρ ν q.1 := by
  obtain ⟨x, hx⟩ := p.2.eval_exists M ρ ν BoundEnv.empty
  obtain ⟨y, hy⟩ := q.2.eval_exists M ρ ν BoundEnv.empty
  exact (holds_iff_of_eval (t := (HOLProp.disj p q).1) (Eval.disj hx hy)).trans
    ((Carrier.truth_disj x y).trans
      (or_congr (holds_iff_of_eval hx).symm (holds_iff_of_eval hy).symm))

theorem holds_disjList {M : Model.{u} S.sig} {ρ : TypeValuation.{u}} {ν : FreeEnv M ρ} :
    ∀ Δ : List (HOLProp S), Holds M ρ ν (HOLProp.disjList Δ).1 ↔ ∃ d ∈ Δ, Holds M ρ ν d.1
  | [] => by simpa [HOLProp.disjList, HOLProp.falsity] using Holds.not_falsity
  | p :: ps => by
    rw [HOLProp.disjList, holds_disj, holds_disjList ps]
    simp

theorem gentzen_iff_seq_disjList (Γ Δ : List (HOLProp S)) :
    gentzen.{u} S Γ Δ ↔ seq.{u} S Γ (HOLProp.disjList Δ) :=
  forall_congr' fun _ => imp_congr_right fun _ => (holds_disjList Δ).symm

theorem derives_le_globalSeq {Δ : List (HOLProp S)} {p : HOLProp S}
    (d : Derives S.sig (Δ.map Subtype.val) ∅ p.1) : globalSeq.{u} S Δ p := by
  intro M hM x
  refine d.sound M (fun a ha => ?_) x.1 x.2 fun _ h => absurd h (Finset.notMem_empty _)
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ha
  exact fun ρ ν => hM q hq ⟨ρ, ν⟩

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
