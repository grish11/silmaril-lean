module

public import Silmaril.Semantics.Accept.IO.Defs
import Silmaril.Proofs.Semantics.Accept.IO.Basic

/-!
# Relational I/O acceptance: laws

* input windows: `mem_windows` (a window is an input occurrence before the scope's exit and the
  outputs after it, up to the next input or the exit);
* runs of a trace: `mem_inputRuns`, `mem_entryRuns` (over every scope ID);
* scope invariance: `localView_insert_other` (events of another scope do not change a local
  view), `inputRuns_congr`/`entryRuns_congr` (traces with the same local views have the same
  runs), and `inputRunsOf_eq`/`entryRunsOf_eq`, `inputRunsOf_congr`/`entryRunsOf_congr`: the
  runs of a trace model depend only on its `ScopeViews`;
* projections: `retTriggers` from `episodes` (`mem_retTriggers`), `returns` as the image of
  `episodes` (`returns_eq_image`), returned triggering implies triggering
  (`triggers_of_mem_retTriggers`) with equality of the projection when every run returns
  (`image_retTriggers_eq`), and failed runs contribute to `triggers` only
  (`mem_episodes_iff_run`);
* transport along renamings of inputs, outputs and results (`triggers_image_map`,
  `episodes_image_map`, `returns_image_map`), and monotonicity.
-/

@[expose] public section

namespace Silmaril.Accept.IO

open scoped Silmaril.Accept

universe u₁ u₂ u₃ u₄ u₅

variable {K : Type u₁} {X : Type u₂} {I : Type u₃} {O : Type u₄} {C : Type u₅}

/-! ## Windows and runs -/

/-- A window is an input occurrence before the scope's exit, with the outputs after it up to
the next input or the exit. -/
theorem mem_windows {l : List (Loc X I O C)} {r : Run I O C} :
    r ∈ windows l ↔ ∃ pre i post, l = pre ++ .inp i :: post ∧ (∀ e ∈ pre, ¬ e.IsExit) ∧
      r = ⟨i, (collect true post).1, (collect true post).2⟩ :=
  Proofs.Semantics.Accept.IO.mem_windows

/-- The entry run of a view that opens with an observed entry. -/
@[simp] theorem entryRun_enter (x : X) (l : List (Loc X I O C)) :
    entryRun (.enter (some x) :: l) = some ⟨x, (collect false l).1, (collect false l).2⟩ := rfl

variable [DecidableEq K]

/-- Events of other scopes are not in a local view. -/
theorem localView_cons_of_ne {k : K} {e : Ev K X I O C} (t : List (Ev K X I O C))
    (he : e.scope ≠ k) : localView k (e :: t) = localView k t := by
  simp [localView, Ev.at, he]

/-- Events of the scope are in its local view. -/
theorem localView_cons_of_eq {k : K} {e : Ev K X I O C} (t : List (Ev K X I O C))
    (he : e.scope = k) : localView k (e :: t) = e.loc :: localView k t := by
  simp [localView, Ev.at, he]

/-- Inserting an event of another scope anywhere does not change a local view. -/
theorem localView_insert_other {k : K} (u v : List (Ev K X I O C)) {e : Ev K X I O C}
    (he : e.scope ≠ k) : localView k (u ++ e :: v) = localView k (u ++ v) :=
  Proofs.Semantics.Accept.IO.localView_insert_other u v he

/-- The input-window runs of a trace are the windows of its scopes. -/
theorem mem_inputRuns {t : List (Ev K X I O C)} {r : Run I O C} :
    r ∈ inputRuns t ↔ ∃ k, r ∈ windows (localView k t) :=
  Proofs.Semantics.Accept.IO.mem_inputRuns

/-- The entry runs of a trace are the entry runs of its scopes. -/
theorem mem_entryRuns {t : List (Ev K X I O C)} {r : Run X O C} :
    r ∈ entryRuns t ↔ ∃ k, entryRun (localView k t) = some r :=
  Proofs.Semantics.Accept.IO.mem_entryRuns

/-- Traces with the same local views (for example, two interleavings of the same scopes) have
the same input-window runs. -/
theorem inputRuns_congr {t t' : List (Ev K X I O C)} (h : ∀ k, localView k t = localView k t')
    (r : Run I O C) : r ∈ inputRuns t ↔ r ∈ inputRuns t' :=
  Proofs.Semantics.Accept.IO.inputRuns_congr h r

/-- Traces with the same local views have the same entry runs. -/
theorem entryRuns_congr {t t' : List (Ev K X I O C)} (h : ∀ k, localView k t = localView k t')
    (r : Run X O C) : r ∈ entryRuns t ↔ r ∈ entryRuns t' :=
  Proofs.Semantics.Accept.IO.entryRuns_congr h r

/-- The input-window runs of a trace model are read off its scope views. -/
theorem inputRunsOf_eq (T : Set (List (Ev K X I O C))) :
    inputRunsOf T = {r | ∃ l ∈ ScopeViews T, r ∈ windows l} :=
  Proofs.Semantics.Accept.IO.inputRunsOf_eq T

/-- The entry runs of a trace model are read off its scope views. -/
theorem entryRunsOf_eq (T : Set (List (Ev K X I O C))) :
    entryRunsOf T = {r | ∃ l ∈ ScopeViews T, entryRun l = some r} :=
  Proofs.Semantics.Accept.IO.entryRunsOf_eq T

/-- Trace models with the same scope views have the same input-window runs, hence the same
`triggers`, `episodes`, `retTriggers` and `returns`. -/
theorem inputRunsOf_congr {K' : Type*} [DecidableEq K'] {T : Set (List (Ev K X I O C))}
    {T' : Set (List (Ev K' X I O C))} (h : ScopeViews T = ScopeViews T') :
    inputRunsOf T = inputRunsOf T' := by
  rw [inputRunsOf_eq, inputRunsOf_eq, h]

/-- Trace models with the same scope views have the same entry runs. -/
theorem entryRunsOf_congr {K' : Type*} [DecidableEq K'] {T : Set (List (Ev K X I O C))}
    {T' : Set (List (Ev K' X I O C))} (h : ScopeViews T = ScopeViews T') :
    entryRunsOf T = entryRunsOf T' := by
  rw [entryRunsOf_eq, entryRunsOf_eq, h]

/-- More traces, more runs. -/
theorem inputRunsOf_mono {T T' : Set (List (Ev K X I O C))} (h : T ⊆ T') :
    inputRunsOf T ⊆ inputRunsOf T' := fun _ ⟨t, ht, hr⟩ => ⟨t, h ht, hr⟩

/-- More traces, more entry runs. -/
theorem entryRunsOf_mono {T T' : Set (List (Ev K X I O C))} (h : T ⊆ T') :
    entryRunsOf T ⊆ entryRunsOf T' := fun _ ⟨t, ht, hr⟩ => ⟨t, h ht, hr⟩

/-! ## Relations of a set of runs -/

section Rel

variable {S S' : Set (Run I O C)} {a : I} {b : O} {bs : List O} {c : C}

@[simp] theorem mem_triggers : (a, b) ∈ triggers S ↔ ∃ r ∈ S, r.input = a ∧ b ∈ r.outputs :=
  Iff.rfl

@[simp] theorem mem_episodes : (a, (bs, c)) ∈ episodes S ↔ ⟨a, bs, some c⟩ ∈ S := Iff.rfl

/-- **(3) is the projection of (2)**: `(a, b, c)` iff `b` is an output of an episode of `a`
returning `c`. -/
@[simp] theorem mem_retTriggers :
    (a, b, c) ∈ retTriggers S ↔ ∃ bs, (a, (bs, c)) ∈ episodes S ∧ b ∈ bs := Iff.rfl

@[simp] theorem mem_returns : (a, c) ∈ returns S ↔ ∃ bs, (a, (bs, c)) ∈ episodes S := Iff.rfl

/-- `returns` forgets the outputs of `episodes`. -/
theorem returns_eq_image (S : Set (Run I O C)) :
    returns S = (fun p => (p.1, p.2.2)) '' episodes S :=
  Proofs.Semantics.Accept.IO.returns_eq_image S

/-- An output of a returned episode is triggered. -/
theorem triggers_of_mem_retTriggers (h : (a, b, c) ∈ retTriggers S) : (a, b) ∈ triggers S :=
  let ⟨_, he, hb⟩ := h; ⟨_, he, rfl, hb⟩

/-- An output of a returned episode belongs to a returning input. -/
theorem returns_of_mem_retTriggers (h : (a, b, c) ∈ retTriggers S) : (a, c) ∈ returns S :=
  let ⟨_, he, _⟩ := h; ⟨_, he⟩

/-- When every run returns, triggering is exactly the projection of returned triggering. Without
this hypothesis a trapped run separates them (`Examples`). -/
theorem image_retTriggers_eq (hS : ∀ r ∈ S, r.result.isSome) :
    (fun p => (p.1, p.2.1)) '' retTriggers S = triggers S :=
  Proofs.Semantics.Accept.IO.image_retTriggers_eq hS

/-- Every output occurrence of every run is triggered, whatever its result. -/
theorem mem_triggers_of_run {r : Run I O C} (hr : r ∈ S) (hb : b ∈ r.outputs) :
    (r.input, b) ∈ triggers S := ⟨r, hr, rfl, hb⟩

/-- Episodes are exactly the runs with a successful result: a run with result `none` (a trap,
a non-returning or cut-off scope) contributes to `triggers` only. -/
theorem mem_episodes_iff_run {p : I × List O × C} :
    p ∈ episodes S ↔ ∃ r ∈ S, r.input = p.1 ∧ r.outputs = p.2.1 ∧ r.result = some p.2.2 :=
  ⟨fun h => ⟨_, h, rfl, rfl, rfl⟩, fun ⟨⟨_, _, _⟩, hr, h₁, h₂, h₃⟩ => by
    subst h₁ h₂ h₃; exact hr⟩

theorem triggers_mono (h : S ⊆ S') : triggers S ⊆ triggers S' :=
  fun _ ⟨r, hr, hi⟩ => ⟨r, h hr, hi⟩

theorem episodes_mono (h : S ⊆ S') : episodes S ⊆ episodes S' := fun _ hp => h hp

theorem retTriggers_mono (h : S ⊆ S') : retTriggers S ⊆ retTriggers S' :=
  fun _ ⟨bs, he, hb⟩ => ⟨bs, h he, hb⟩

theorem returns_mono (h : S ⊆ S') : returns S ⊆ returns S' :=
  fun _ ⟨bs, he⟩ => ⟨bs, h he⟩

variable {I' : Type*} {O' : Type*} {C' : Type*} (f : I → I') (g : O → O') (h : C → C')

/-- Triggering transports along renamings. -/
theorem triggers_image_map : triggers (Run.map f g h '' S) = Prod.map f g '' triggers S :=
  Proofs.Semantics.Accept.IO.triggers_image_map f g h

/-- Episodes transport along renamings. -/
theorem episodes_image_map :
    episodes (Run.map f g h '' S) = Prod.map f (Prod.map (List.map g) h) '' episodes S :=
  Proofs.Semantics.Accept.IO.episodes_image_map f g h

/-- Returns transport along renamings. -/
theorem returns_image_map : returns (Run.map f g h '' S) = Prod.map f h '' returns S := by
  rw [returns_eq_image, returns_eq_image, episodes_image_map, Set.image_image, Set.image_image]
  rfl

end Rel

end Silmaril.Accept.IO
