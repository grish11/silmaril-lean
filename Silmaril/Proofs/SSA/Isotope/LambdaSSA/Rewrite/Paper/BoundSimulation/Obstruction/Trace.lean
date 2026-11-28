module

public import Silmaril.SSA.Isotope.LambdaSSA.Defs

/-! # Finite CFG traces

A CFG reports a finite jump or fault when its trace reaches one. An infinite
trace reports divergence. The continuation laws preserve local trace steps.
-/

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region

abbrev Val := Value Empty

inductive Result where
  | jump (label : Nat) (value : Val)
  | diverges
  | fault

abbrev Frame (n : Nat) := Result ⊕ (Fin n × Val)

def enter (n : Nat) : Result → Frame n
  | .jump i v => if h : i < n then .inr (⟨i, h⟩, v) else .inl (.jump (i - n) v)
  | .diverges => .inl (.diverges)
  | .fault => .inl .fault

def step {n : Nat} (bs : Fin n → Val → Result) : Frame n → Frame n
  | .inl result => .inl result
  | .inr (i, v) => enter n (bs i v)

def path {n : Nat} (bs : Fin n → Val → Result) (start : Frame n) : Nat → Frame n
  | 0 => start
  | k + 1 => step bs (path bs start k)

theorem path_add {n : Nat} (bs : Fin n → Val → Result) (start : Frame n) (j k : Nat) :
    path bs start (j + k) = path bs (path bs start j) k := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (step bs) ih

theorem path_absorb {n : Nat} (bs : Fin n → Val → Result) (r : Result) (k : Nat) :
    path bs (.inl r) k = .inl r := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [path, ih, step]

theorem terminal_unique {n : Nat} (bs : Fin n → Val → Result) (start : Frame n)
    {j k : Nat} {r s : Result} (hr : path bs start j = .inl r) (hs : path bs start k = .inl s) : r = s := by
  rcases Nat.le_total j k with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [path_add, hr, path_absorb] at hs
    exact Sum.inl.inj hs
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [path_add, hs, path_absorb] at hr
    exact (Sum.inl.inj hr).symm

def terminates {n : Nat} (bs : Fin n → Val → Result) (start : Frame n) (r : Result) : Prop :=
  ∃ k, path bs start k = .inl r

def loopResult : Bool → Result
  | false => .diverges
  | true => .fault

noncomputable def finish {n : Nat} (bs : Fin n → Val → Result) (start : Frame n) (mark : Bool := false) : Result := by
  classical
  exact if h : ∃ r, terminates bs start r then h.choose
    else loopResult mark

theorem finish_of_terminal {n : Nat} (bs : Fin n → Val → Result) (start : Frame n)
    {k : Nat} {r : Result} {mark : Bool} (hr : path bs start k = .inl r) : finish bs start mark = r := by
  have h : ∃ r, terminates bs start r := ⟨r, k, hr⟩
  rw [finish, dite_eq_left h]
  obtain ⟨j, hj⟩ := h.choose_spec
  exact terminal_unique bs start hj hr

theorem terminates_step_iff {n : Nat} (bs : Fin n → Val → Result)
    (start : Frame n) (r : Result) : terminates bs (step bs start) r ↔ terminates bs start r := by
  have shift (k : Nat) : path bs (step bs start) k = path bs start (1 + k) :=
    (path_add bs start 1 k).symm
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨1 + k, (shift k).symm.trans hk⟩
  · rintro ⟨k, hk⟩
    cases k with
    | zero =>
      change start = .inl r at hk
      exact ⟨0, by rw [hk]; rfl⟩
    | succ k =>
      exact ⟨k, (shift k).trans (by simpa only [Nat.one_add] using hk)⟩

theorem finish_step {n : Nat} {mark : Bool} (bs : Fin n → Val → Result) (start : Frame n) :
    finish bs (step bs start) mark = finish bs start mark := by
  classical
  by_cases h : ∃ r, terminates bs start r
  · obtain ⟨r, k, hk⟩ := h
    obtain ⟨j, hj⟩ := (terminates_step_iff bs start r).mpr ⟨k, hk⟩
    rw [finish_of_terminal bs _ hj, finish_of_terminal bs _ hk]
  · have h' : ¬ ∃ r, terminates bs (step bs start) r :=
      fun ⟨r, hr⟩ => h ⟨r, (terminates_step_iff bs start r).mp hr⟩
    rw [finish, dite_eq_right h', finish, dite_eq_right h]

noncomputable def cfgRun (n : Nat) (bs : Fin n → Val → Result) (entry : Result)
    (mark : Bool := false) : Result :=
  finish bs (enter n entry) mark

theorem cfgRun_out {n i : Nat} {mark : Bool} (bs : Fin n → Val → Result) (v : Val) (hi : n ≤ i) :
    cfgRun n bs (.jump i v) mark = .jump (i - n) v := by
  apply finish_of_terminal bs _ (k := 0)
  simp [path, enter, Nat.not_lt_of_ge hi]

theorem cfgRun_local {n i : Nat} {mark : Bool} (bs : Fin n → Val → Result) (v : Val) (hi : i < n) :
    cfgRun n bs (.jump i v) mark = cfgRun n bs (bs ⟨i, hi⟩ v) mark := by
  change finish bs (enter n (.jump i v)) mark = _
  rw [enter, dite_eq_left hi, ← finish_step bs (.inr (⟨i, hi⟩, v))]
  rfl

/-- Transform terminal outcomes while preserving each local state. -/
def mapTerminal {n : Nat} (k : Result → Result) : Frame n → Frame n
  | .inl r => .inl (k r)
  | .inr s => .inr s

theorem finish_mapTerminalOn {n : Nat} {mark : Bool} (bs bs' : Fin n → Val → Result)
    (k : Result → Result) (keep : k (loopResult mark) = loopResult mark)
    (good : Frame n → Prop) (stable : ∀ s, good s → good (step bs s))
    (comm : ∀ s, good s → step bs' (mapTerminal k s) = mapTerminal k (step bs s))
    (start : Frame n) (hstart : good start) :
    finish bs' (mapTerminal k start) mark = k (finish bs start mark) := by
  classical
  have pathGood (i : Nat) : good (path bs start i) := by
    induction i with
    | zero => exact hstart
    | succ i ih => exact stable _ ih
  have paths (i : Nat) : path bs' (mapTerminal k start) i = mapTerminal k (path bs start i) := by
    induction i with
    | zero => rfl
    | succ i ih => rw [path, path, ih, comm _ (pathGood i)]
  by_cases hf : ∃ r, terminates bs start r
  · obtain ⟨r, i, hi⟩ := hf
    have hi' : path bs' (mapTerminal k start) i = .inl (k r) := by
      rw [paths, hi]
      rfl
    rw [finish_of_terminal bs' _ hi', finish_of_terminal bs _ hi]
  · have hf' : ¬ ∃ r, terminates bs' (mapTerminal k start) r := by
      rintro ⟨r, i, hi⟩
      rw [paths] at hi
      cases h : path bs start i with
      | inl r => exact hf ⟨r, i, h⟩
      | inr s => rw [h] at hi; cases hi
    rw [finish, dite_eq_right hf', finish, dite_eq_right hf, keep]

theorem finish_mapTerminal {n : Nat} {mark : Bool} (bs bs' : Fin n → Val → Result)
    (k : Result → Result) (keep : k (loopResult mark) = loopResult mark)
    (comm : ∀ s, step bs' (mapTerminal k s) = mapTerminal k (step bs s))
    (start : Frame n) : finish bs' (mapTerminal k start) mark = k (finish bs start mark) :=
  finish_mapTerminalOn bs bs' k keep (fun _ => True)
    (fun _ _ => trivial) (fun s _ => comm s) start trivial

def mapOut (k : Nat → Val → Result) : Result → Result
  | .jump i v => k i v
  | .diverges => .diverges
  | .fault => .fault

theorem mapOut_loopResult (k : Nat → Val → Result) (mark : Bool) :
    mapOut k (loopResult mark) = loopResult mark := by
  cases mark <;> rfl

def shiftOut (n : Nat) : Result → Result :=
  mapOut (fun i v => .jump (n + i) v)

def insideMap (n : Nat) (k : Nat → Val → Result) : Result → Result :=
  mapOut (fun i v => if i < n then .jump i v else shiftOut n (k (i - n) v))

theorem enter_shiftOut (n : Nat) (r : Result) : enter n (shiftOut n r) = .inl r := by
  cases r with
  | jump i v => simp [shiftOut, mapOut, enter, Nat.not_lt_of_ge (Nat.le_add_right n i)]
  | diverges => rfl
  | fault => rfl

theorem enter_insideMap (n : Nat) (k : Nat → Val → Result) (r : Result) :
    enter n (insideMap n k r) = mapTerminal (mapOut k) (enter n r) := by
  cases r with
  | jump i v =>
    by_cases h : i < n
    · simp [insideMap, mapOut, enter, mapTerminal, h]
    · rw [insideMap, mapOut, ite_eq_right h, enter_shiftOut, enter, dite_eq_right h]
      rfl
  | diverges => rfl
  | fault => rfl

theorem cfgRun_mapOut {mark : Bool} (n : Nat) (bs : Fin n → Val → Result)
    (k : Nat → Val → Result) (r : Result) :
    cfgRun n (fun i v => insideMap n k (bs i v)) (insideMap n k r) mark =
      mapOut k (cfgRun n bs r mark) := by
  change finish _ (enter n (insideMap n k r)) mark = mapOut k (finish bs (enter n r) mark)
  rw [enter_insideMap]
  refine finish_mapTerminal bs _ (mapOut k) (mapOut_loopResult k mark) ?_ _
  intro s
  cases s with
  | inl r => rfl
  | inr s =>
    obtain ⟨i, v⟩ := s
    exact enter_insideMap n k (bs i v)

theorem cfgRun_diverges {mark : Bool} (n : Nat) (bs : Fin n → Val → Result) :
    cfgRun n bs .diverges mark = .diverges :=
  finish_of_terminal bs _ (k := 0) rfl

theorem cfgRun_fault {mark : Bool} (n : Nat) (bs : Fin n → Val → Result) :
    cfgRun n bs .fault mark = .fault :=
  finish_of_terminal bs _ (k := 0) rfl

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer
