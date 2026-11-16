module

public import Silmaril.Containers.Mini.Defs
public import Silmaril.Containers.Machine.Thms

/-!
# Proofs: the minimal machine

Proofs for `Silmaril.Containers.Mini.Thms`. Nothing imports this module except that header.
-/

@[expose] public section

namespace Silmaril.Proofs.Containers.Mini

open Silmaril.Containers Silmaril.Containers.Mach Silmaril.Containers.Mini

theorem step_tau {s s' : List Instr} (h : mini.step s .tau s') : s' = s ∧ ∃ r, s = .spin :: r := by
  rcases s with _ | ⟨i, rest⟩
  · exact h.elim
  · cases i <;> simp at h
    exact ⟨h, rest, rfl⟩

theorem step_ev {s s' : List Instr} {e : Ev} (h : mini.step s (.ev e) s') : s = .emit e :: s' := by
  rcases s with _ | ⟨i, rest⟩
  · exact h.elim
  · cases i <;> simp at h
    obtain ⟨rfl, rfl⟩ := h; rfl

theorem step_clone {s s' : List Instr} {r : CloneReq} (h : mini.step s (.clone r) s') :
    s = .clone r :: s' := by
  rcases s with _ | ⟨i, rest⟩
  · exact h.elim
  · cases i <;> simp at h
    obtain ⟨rfl, rfl⟩ := h; rfl

theorem exec_inv {s s' : mini.State} {t : List Ev} (h : mini.Exec s t s') :
    (s : List Instr) = t.map .emit ++ s' := by
  induction h with
  | refl => rfl
  | tau hs _ ih => exact (step_tau hs).1 ▸ ih
  | ev hs _ ih => rw [step_ev hs, ih]; rfl

theorem exec_emits (es : List Ev) (q : List Instr) : mini.Exec (es.map .emit ++ q) es q := by
  induction es with
  | nil => exact .refl _
  | cons e es ih => exact .ev (s' := es.map .emit ++ q) ⟨rfl, rfl⟩ ih

theorem result_emits (es : List Ev) (q : List Instr) :
    result (es.map .emit ++ q) = es.foldr cons (result q) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [List.map_cons, List.cons_append, result, ih, List.foldr_cons]

theorem foldr_done (es t : List Ev) (s : Stop) :
    es.foldr cons (.done t s) = .done (es ++ t) s := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [List.foldr_cons, ih, cons, List.cons_append]

theorem foldr_spins (es t : List Ev) : es.foldr cons (.spins t) = .spins (es ++ t) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [List.foldr_cons, ih, cons, List.cons_append]

theorem splitEmits (p : List Instr) :
    ∃ (es : List Ev) (q : List Instr), p = es.map .emit ++ q ∧ ∀ e r, q ≠ .emit e :: r := by
  induction p with
  | nil => exact ⟨[], [], rfl, fun _ _ h => nomatch h⟩
  | cons i p ih =>
    by_cases hi : ∃ e, i = .emit e
    · obtain ⟨e, rfl⟩ := hi
      obtain ⟨es, q, rfl, hq⟩ := ih
      exact ⟨e :: es, q, rfl, hq⟩
    · exact ⟨[], i :: p, rfl, fun e r h => hi ⟨e, (List.cons.inj h).1⟩⟩

theorem final_result {s : List Instr} {st : Stop} (h : mini.final s st) :
    result s = .done [] st := by
  rcases s with _ | ⟨i, rest⟩
  · exact h.elim
  · cases i <;> simp at h <;> (subst h; rfl)

theorem stuck_result {s : List Instr} (h : mini.Stuck s) : result s = .done [] (.undefined .stuck) := by
  rcases s with _ | ⟨i, rest⟩
  · rfl
  · cases i with
    | emit e => exact (h.1 (.ev e) rest ⟨rfl, rfl⟩).elim
    | clone r => exact (h.1 (.clone r) rest ⟨rfl, rfl⟩).elim
    | exit c => exact (h.2 (.exited c) rfl).elim
    | crash g => exact (h.2 (.signaled g) rfl).elim
    | spin => exact (h.1 .tau _ ⟨rfl, rfl⟩).elim

theorem runs_iff {p : List Instr} (hp : OutputOnly p) (b : Beh Ev) :
    mini.Run p b ↔ b = result p := by
  constructor
  · intro h
    cases h with
    | @final s s' t st hs hx hf =>
      subst hs
      rw [exec_inv hx, result_emits, final_result hf, foldr_done, List.append_nil]
    | @clone s s' s'' t r hs hx hc =>
      subst hs
      rw [exec_inv hx, result_emits, step_clone hc,
        show result (Instr.clone r :: s'') = .done [] (.undefined r.ub) from rfl, foldr_done,
        List.append_nil]
    | @stuck s s' t hs hx hst =>
      subst hs
      rw [exec_inv hx, result_emits, stuck_result hst, foldr_done, List.append_nil]
    | @blocked s s' t hs hx hw =>
      subst hs
      obtain ⟨e, s'', hin, he⟩ := hw.2.1
      have hmem : Instr.emit e ∈ s := by
        rw [exec_inv hx, step_ev he]; simp
      have hin' : e.isInput = true := hin
      rw [hp e hmem] at hin'; cases hin'
    | @spins s s' t hs hx hd =>
      subst hs
      obtain ⟨f, hf0, hf⟩ := hd
      obtain ⟨-, r, hr⟩ := step_tau (hf 0)
      rw [hf0] at hr
      rw [exec_inv hx, result_emits, hr, show result (Instr.spin :: r) = .spins [] from rfl,
        foldr_spins, List.append_nil]
    | reactive f hf =>
      obtain ⟨s, s', hs, hx⟩ := hf (p.length + 1)
      subst hs
      have := congrArg List.length (exec_inv hx)
      simp at this
      omega
    | noInit h => exact (h p rfl).elim
  · rintro rfl
    obtain ⟨es, q, rfl, hq⟩ := splitEmits p
    rw [result_emits]
    rcases q with _ | ⟨i, rest⟩
    · rw [show result [] = .done [] (.undefined .stuck) from rfl, foldr_done, List.append_nil es]
      exact .stuck (s' := ([] : List Instr)) rfl (exec_emits es [])
        ⟨fun _ _ h => h, fun _ h => h⟩
    · cases i with
      | emit e => exact (hq e rest rfl).elim
      | clone r =>
        rw [show result (.clone r :: rest) = .done [] (.undefined r.ub) from rfl, foldr_done,
          List.append_nil]
        exact .clone rfl (exec_emits es _) (s'' := rest) ⟨rfl, rfl⟩
      | exit c =>
        rw [show result (.exit c :: rest) = .done [] (.exited c) from rfl, foldr_done,
          List.append_nil]
        exact .final rfl (exec_emits es _) rfl
      | crash g =>
        rw [show result (.crash g :: rest) = .done [] (.signaled g) from rfl, foldr_done,
          List.append_nil]
        exact .final rfl (exec_emits es _) rfl
      | spin =>
        rw [show result (.spin :: rest) = .spins [] from rfl, foldr_spins, List.append_nil]
        exact .spins rfl (exec_emits es _) ⟨fun _ => .spin :: rest, rfl, fun _ => ⟨rfl, rfl⟩⟩

theorem beh_mimage {p : List Instr} (hp : OutputOnly p) (b : Beh Ev) :
    machRT.beh (mimage p) b ↔ b = result p := by
  rw [Runtime.beh_ok (R := machRT) (i := mimage p) (p := p) rfl]
  exact ⟨fun ⟨_, h, he⟩ => he ▸ (runs_iff hp _).1 h, fun h => ⟨b, (runs_iff hp _).2 h, rfl⟩⟩

theorem wlp_iff {p : List Instr} (hp : OutputOnly p) (post : List Ev → UInt8 → Prop) :
    wlp machRT post (mimage p) ↔ Spec.noUB (result p) ∧ Spec.partialCorrect post (result p) :=
  ⟨fun h => h _ ((beh_mimage hp _).2 rfl), fun h b hb => ((beh_mimage hp b).1 hb) ▸ h⟩

theorem wp_iff {p : List Instr} (hp : OutputOnly p) (post : List Ev → UInt8 → Prop) :
    wp machRT post (mimage p) ↔ Spec.noUB (result p) ∧ Spec.totalCorrect post (result p) :=
  ⟨fun h => h _ ((beh_mimage hp _).2 rfl), fun h b hb => ((beh_mimage hp b).1 hb) ▸ h⟩

theorem pre_iff {p : List Instr} (hp : OutputOnly p) (φ : Spec Ev) :
    pre machRT φ (mimage p) ↔ φ (result p) :=
  ⟨fun h => h _ ((beh_mimage hp _).2 rfl), fun h b hb => ((beh_mimage hp b).1 hb) ▸ h⟩

end Silmaril.Proofs.Containers.Mini
