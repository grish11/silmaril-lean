module

public import Silmaril.SSA.Isotope.LetCase.HandledTrace.Category.Tensor.Defs

public section

namespace Silmaril.Isotope.LetCase.HandledTrace.TensorProofs

open LocallyNameless Silmaril.Isotope.Semantics Silmaril.Elgot.ITree

universe u v e s

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {D : τ → Type (e + 1)} [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
  {Events : Type e → Type e} {State : Type s}
  {M : InstructionModel D Φ (Tree Events)} {policy : Handler State Events}
  {A B C K : τ}

local notation "prod" => ProductModel.productEquiv (D := D)

theorem run_fst (a : D A) (b : D B) :
    (Program.fst (Φ := Φ) A B).run M ((prod A B).symm (a, b)) = pure a := by
  change ((pure ((prod A B).symm (a, b)) : Tree Events (D (product A B))) >>= fun ab =>
    pure (prod A B ab).1) = pure a
  rw [pure_bind, Equiv.apply_symm_apply]

theorem run_snd (a : D A) (b : D B) :
    (Program.snd (Φ := Φ) A B).run M ((prod A B).symm (a, b)) = pure b := by
  change ((pure ((prod A B).symm (a, b)) : Tree Events (D (product A B))) >>= fun ab =>
    pure (prod A B ab).2) = pure b
  rw [pure_bind, Equiv.apply_symm_apply]

theorem run_pair (p : Program Φ A B) (q : Program Φ A C) (a : D A) :
    (p.pair q).run M a =
      (p.run M a >>= fun b => q.run M a >>= fun c => pure ((prod B C).symm (b, c))) :=
  rfl

theorem run_left (p : Program Φ A B) (k : D K) (a : D A) :
    (p.whiskerLeft K).run M ((prod K A).symm (k, a)) =
      (p.run M a >>= fun b => pure ((prod K B).symm (k, b))) := by
  simp only [Program.whiskerLeft, run_pair, Program.run_seq, run_fst, run_snd, pure_bind]

theorem run_right (p : Program Φ A B) (a : D A) (k : D K) :
    (p.whiskerRight K).run M ((prod A K).symm (a, k)) =
      (p.run M a >>= fun b => pure ((prod B K).symm (b, k))) := by
  simp only [Program.whiskerRight, run_pair, Program.run_seq, run_fst, run_snd, pure_bind]

private theorem replay_map_result {U V : Type (e + 1)} (f : U → V)
    (trace : Trace Events U) (state : State) :
    Replay policy state (trace.map f) ↔ Replay policy state trace := by
  induction trace generalizing state with
  | «prefix» | request | result => rfl
  | exchange event reply tail ih =>
    simp only [Trace.map, Replay, ih]

/-- Mapping the result preserves each exact path admitted at the same state. -/
theorem handled_map_iff {U V : Type (e + 1)} (f : U → V) (tree : Tree Events U)
    (state : State) (trace : Trace Events V) :
    HandledTrace policy state (tree >>= fun a => pure (f a)) trace ↔
      ∃ original, HandledTrace policy state tree original ∧ original.map f = trace := by
  constructor
  · rintro ⟨observed, admitted⟩
    obtain ⟨original, hasTrace, rfl⟩ := (hasTrace_bind_pure_iff f tree trace).mp observed
    exact ⟨original, ⟨hasTrace, (replay_map_result f original state).mp admitted⟩, rfl⟩
  · rintro ⟨original, ⟨observed, admitted⟩, rfl⟩
    exact ⟨(hasTrace_bind_pure_iff f tree _).mpr ⟨original, observed, rfl⟩,
      (replay_map_result f original state).mpr admitted⟩

theorem left_mono {p q : Program Φ A B} (K : τ) (h : Program.Refines M policy p q) :
    Program.Refines M policy (p.whiskerLeft K) (q.whiskerLeft K) := by
  intro input state
  obtain ⟨⟨k, a⟩, rfl⟩ := (prod K A).symm.surjective input
  rw [run_left, run_left]
  exact (h a state).bind_left _

theorem right_mono {p q : Program Φ A B} (K : τ) (h : Program.Refines M policy p q) :
    Program.Refines M policy (p.whiskerRight K) (q.whiskerRight K) := by
  intro input state
  obtain ⟨⟨a, k⟩, rfl⟩ := (prod A K).symm.surjective input
  rw [run_right, run_right]
  exact (h a state).bind_left _

theorem left_id (K A : τ) :
    (Program.setoid M policy (product K A) (product K A)).r
      ((Program.id A).whiskerLeft K) (Program.id (product K A)) := by
  apply Program.equiv_of_run_eq
  intro input
  obtain ⟨⟨k, a⟩, rfl⟩ := (prod K A).symm.surjective input
  rw [run_left]
  exact pure_bind _ _

theorem right_id (K A : τ) :
    (Program.setoid M policy (product A K) (product A K)).r
      ((Program.id A).whiskerRight K) (Program.id (product A K)) := by
  apply Program.equiv_of_run_eq
  intro input
  obtain ⟨⟨a, k⟩, rfl⟩ := (prod A K).symm.surjective input
  rw [run_right]
  exact pure_bind _ _

theorem left_seq (K : τ) (p : Program Φ A B) (q : Program Φ B C) :
    (Program.setoid M policy (product K A) (product K C)).r
      ((p.seq q).whiskerLeft K) ((p.whiskerLeft K).seq (q.whiskerLeft K)) := by
  apply Program.equiv_of_run_eq
  intro input
  obtain ⟨⟨k, a⟩, rfl⟩ := (prod K A).symm.surjective input
  simp only [run_left, Program.run_seq, bind_assoc]
  apply bind_congr
  intro b
  rw [pure_bind, run_left]

theorem right_seq (K : τ) (p : Program Φ A B) (q : Program Φ B C) :
    (Program.setoid M policy (product A K) (product C K)).r
      ((p.seq q).whiskerRight K) ((p.whiskerRight K).seq (q.whiskerRight K)) := by
  apply Program.equiv_of_run_eq
  intro input
  obtain ⟨⟨a, k⟩, rfl⟩ := (prod A K).symm.surjective input
  simp only [run_right, Program.run_seq, bind_assoc]
  apply bind_congr
  intro b
  rw [pure_bind, run_right]

end Silmaril.Isotope.LetCase.HandledTrace.TensorProofs
