module

public import Silmaril.Logic.Temporal.FiniteAutomaton.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Temporal.FiniteAutomaton
open ModalMu Buchi.Automaton

/-- The inductive run and explicit bounded coherent witnesses describe the same paths. -/
theorem run_iff_path {Atom W : Type} {n : Nat} (F : Symbolic Atom n)
    (R : W → W → Prop) (label : W → Atom → Prop) (w : W) (q : Fin n) :
    RunFrom F R label w q ↔ PathRunFrom F R label w q := by
  constructor
  · show RunFrom F R label w q → PathRunFrom F R label w q
    intro h
    induction h with
    | terminal ht hd =>
        exact ⟨0, fun _ => _, fun _ => _, rfl, rfl,
          fun i hi => (Nat.not_lt_zero i hi).elim, ht, hd⟩
    | @step w q v r hg he h ih =>
        show PathRunFrom F R label w q
        obtain ⟨length, path, run, h0, r0, edges, ht, hd⟩ := ih
        refine ⟨length+1, (fun i => Nat.casesOn i w path),
          (fun i => Nat.casesOn i q run), rfl, rfl, ?_, ht, hd⟩
        intro i hi
        cases i with
        | zero =>
            change R w (path 0) ∧ (F.guard q (run 0)).Holds (label w)
            rw [h0, r0]
            exact ⟨he, hg⟩
        | succ i => exact edges i (by omega)
  · show PathRunFrom F R label w q → RunFrom F R label w q
    rintro ⟨length, path, run, h0, r0, edges, ht, hd⟩
    suffices h : RunFrom F R label (path 0) (run 0) by simpa only [h0, r0] using h
    clear h0 r0 w q
    induction length generalizing path run with
    | zero => exact .terminal ht hd
    | succ length ih =>
        have e : R (path 0) (path 1) ∧ (F.guard (run 0) (run 1)).Holds (label (path 0)) :=
          edges 0 (Nat.zero_lt_succ length)
        refine .step e.2 e.1 (ih (fun i => path (i+1)) (fun i => run (i+1)) ?_ ht hd)
        intro i hi
        exact edges (i+1) (by omega)

theorem system_operator {S : Signature} {n : Nat} (F : Symbolic S.Atom n) (a : S.Action)
    (M : Model S) (ρ : Env M.World 0) (X : Env M.World n) (q : Fin n) (w : M.World) :
    w ∈ (system F a).operator M ρ X q ↔
      ((F.terminal q).Holds (modelLabel M w) ∧ ∀ v, ¬ M.step a w v) ∨
      ∃ r v, (F.guard q r).Holds (modelLabel M w) ∧ M.step a w v ∧ v ∈ X r := by
  have hx (r : Fin n) :
      (Formula.var (Fin.castAdd 0 r) : Formula S (n+0)).denote M
        (FiniteVector.joinEnv ρ X) = X r := by
    change Fin.addCases X ρ (Fin.castAdd 0 r) = X r
    exact Fin.addCases_left r
  change (w ∈ (F.terminal q).toFormula.denote M (FiniteVector.joinEnv ρ X) ∧
    (∀ v, M.step a w v → False)) ∨
    w ∈ (Base.disjoin (fun r => .conj (F.guard q r).toFormula
      (.diamond a (.var (Fin.castAdd 0 r))))).denote M (FiniteVector.joinEnv ρ X) ↔ _
  rw [Guard.toFormula_denote, Base.disjoin_denote]
  constructor
  · rintro (ht | ⟨r, hg, v, he, hv⟩)
    · exact Or.inl ht
    · exact Or.inr ⟨r, v, (Guard.toFormula_denote M _ _ w).mp hg, he, (hx r) ▸ hv⟩
  · rintro (ht | ⟨r, v, hg, he, hv⟩)
    · exact Or.inl ht
    · exact Or.inr ⟨r, (Guard.toFormula_denote M _ _ w).mpr hg, v, he, (hx r).symm ▸ hv⟩

/-- The simultaneous least block contains exactly the independently finite runs. -/
theorem system_correct {S : Signature} {n : Nat} (F : Symbolic S.Atom n) (a : S.Action)
    (M : Model S) (ρ : Env M.World 0) (w : M.World) (q : Fin n) :
    w ∈ (system F a).denote false M ρ q ↔ RunFrom F (M.step a) (modelLabel M) w q := by
  let op := (system F a).operator M ρ
  change w ∈ op.lfp q ↔ _
  constructor
  · have hle : op.lfp ≤ (fun r => {v | RunFrom F (M.step a) (modelLabel M) v r}) := by
      apply op.lfp_le
      intro r v hv
      rcases (system_operator F a M ρ _ r v).mp hv with ⟨ht, hd⟩ | ⟨s, u, hg, he, hu⟩
      · exact .terminal ht hd
      · exact RunFrom.step hg he hu
    exact fun h => hle q h
  · show RunFrom F (M.step a) (modelLabel M) w q → w ∈ op.lfp q
    intro h
    induction h with
    | @terminal w q ht hd =>
        have hu : w ∈ op op.lfp q := (system_operator F a M ρ op.lfp _ _).mpr (Or.inl ⟨ht, hd⟩)
        simpa only [op.map_lfp] using hu
    | @step w q v r hg he h ih =>
        have hu : w ∈ op op.lfp q := (system_operator F a M ρ op.lfp _ _).mpr (Or.inr ⟨_, _, hg, he, ih⟩)
        simpa only [op.map_lfp] using hu

/-- Each scalar coordinate denotes one finite path/run from that coordinate. -/
theorem coordinate_correct {S : Signature} {n : Nat} (F : Symbolic S.Atom n)
    (a : S.Action) (M : Model S) (ρ : Env M.World 0) (w : M.World) (q : Fin n) :
    w ∈ (coordinate F a q).denote M ρ ↔ PathRunFrom F (M.step a) (modelLabel M) w q := by
  have hc := congrFun (FiniteVector.System.compile_correct false (system F a) M ρ) q
  rw [coordinate, hc, system_correct, run_iff_path]

/-- Closed scalar syntax on original worlds, with one coherent finite accepting path. -/
theorem formula_correct {S : Signature} {n : Nat} (F : Symbolic S.Atom n)
    (a : S.Action) (M : Model S) (ρ : Env M.World 0) (w : M.World) :
    w ∈ (formula F a).denote M ρ ↔ AcceptsPath F (M.step a) (modelLabel M) w := by
  classical
  rw [formula, Base.disjoin_denote]
  constructor
  · rintro ⟨q, hq⟩
    by_cases hi : q ∈ F.initial
    · exact ⟨q, hi, (coordinate_correct F a M ρ w q).mp (by simpa only [hi, ↓reduceIte] using hq)⟩
    · simp only [hi, ↓reduceIte] at hq
      exact False.elim hq
  · rintro ⟨q, hi, hq⟩
    exact ⟨q, by simpa only [hi, ↓reduceIte] using (coordinate_correct F a M ρ w q).mpr hq⟩

/-- Model-level satisfaction at its actual distinguished original world. -/
theorem sat_iff {S : Signature} {n : Nat} (F : Symbolic S.Atom n)
    (a : S.Action) (M : Model S) :
    Sat M (formula F a) ↔ AcceptsPath F (M.step a) (modelLabel M) M.point :=
  formula_correct F a M emptyEnv M.point

/-- The same semantics in the finite inductive run presentation. -/
theorem formula_iff_run {S : Signature} {n : Nat} (F : Symbolic S.Atom n)
    (a : S.Action) (M : Model S) (ρ : Env M.World 0) (w : M.World) :
    w ∈ (formula F a).denote M ρ ↔ ∃ q ∈ F.initial,
      RunFrom F (M.step a) (modelLabel M) w q := by
  rw [formula_correct]
  exact exists_congr fun q => and_congr_right fun _ => (run_iff_path F _ _ w q).symm

/-- A finite run cannot terminate on a graph where every world has a successor. -/
theorem no_run_of_serial {Atom W : Type} {n : Nat} (F : Symbolic Atom n)
    (R : W → W → Prop) (label : W → Atom → Prop) (serial : ∀ w, ∃ v, R w v)
    (w : W) (q : Fin n) : ¬ RunFrom F R label w q := by
  intro h
  induction h with
  | terminal _ hd => obtain ⟨v, hv⟩ := serial _; exact hd v hv
  | step _ _ _ ih => exact ih

/-- Every finite run reaches a terminal guard on the same graph. -/
theorem run_has_terminal {Atom W : Type} {n : Nat} (F : Symbolic Atom n)
    (R : W → W → Prop) (label : W → Atom → Prop) {w : W} {q : Fin n}
    (h : RunFrom F R label w q) : ∃ v r,
      (F.terminal r).Holds (label v) ∧ (∀ u, ¬ R v u) := by
  induction h with
  | terminal ht hd => exact ⟨_, _, ht, hd⟩
  | step _ _ _ ih => exact ih

end Silmaril.Logic.Temporal.FiniteAutomaton
