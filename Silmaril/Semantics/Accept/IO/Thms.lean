module

public import Silmaril.Semantics.Accept.IO.Defs
import Silmaril.Proofs.Semantics.Accept.IO.Basic
import Silmaril.Proofs.Semantics.Accept.IO.Scope

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
  `episodes_image_map`, `returns_image_map`), and monotonicity;
* provenance (runs back to the events and tags they were read from): `out_mem_of_collect`,
  `exit_mem_of_collect`, `out_mem_of_windows`, `inp_mem_of_windows`, `sublist_of_windows`,
  `out_mem_of_entryRun`, `loc_of_at`, `exists_out_of_mem_localView`,
  `exists_inp_of_mem_localView`, `localView_sublist`;
* scope assignment: `tag_mem_of_mem_assign`, `assign_scope`, `localView_assign_lt`,
  `assign_nil_append`, `map_loc_assign_sublist`.
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

/-! ## Provenance: runs back to events -/

section Provenance

open scoped List

/-- An output collected from a view is an output event of the view. -/
theorem out_mem_of_collect {stop : Bool} {o : O} {l : List (Loc X I O C)}
    (h : o ∈ (collect stop l).1) : .out o ∈ l :=
  Proofs.Semantics.Accept.IO.out_mem_of_collect h

/-- A collected result is an exit event of the view. -/
theorem exit_mem_of_collect {stop : Bool} {c : C} {l : List (Loc X I O C)}
    (h : (collect stop l).2 = some c) : .exit (some c) ∈ l :=
  Proofs.Semantics.Accept.IO.exit_mem_of_collect h

/-- An output of a window is an output event of the view. -/
theorem out_mem_of_windows {l : List (Loc X I O C)} {r : Run I O C} {b : O}
    (hr : r ∈ windows l) (hb : b ∈ r.outputs) : Loc.out b ∈ l :=
  Proofs.Semantics.Accept.IO.out_mem_of_windows hr hb

/-- The input of a window is an input event of the view. -/
theorem inp_mem_of_windows {l : List (Loc X I O C)} {r : Run I O C} (hr : r ∈ windows l) :
    Loc.inp r.input ∈ l :=
  Proofs.Semantics.Accept.IO.inp_mem_of_windows hr

/-- A window is read off the events after its input, which come in order in the view. -/
theorem sublist_of_windows {l : List (Loc X I O C)} {r : Run I O C} (hr : r ∈ windows l) :
    ∃ post, [.inp r.input] ++ post <+ l ∧ r.outputs = (collect true post).1 ∧
      r.result = (collect true post).2 :=
  Proofs.Semantics.Accept.IO.sublist_of_windows hr

/-- An output of an entry run is an output event of the view. -/
theorem out_mem_of_entryRun {l : List (Loc X I O C)} {r : Run X O C} {b : O}
    (hr : entryRun l = some r) (hb : b ∈ r.outputs) : Loc.out b ∈ l :=
  Proofs.Semantics.Accept.IO.out_mem_of_entryRun hr hb

/-- The local event of a scoped event is its `loc`. -/
theorem loc_of_at {k : K} {e : Ev K X I O C} {l : Loc X I O C} (h : Ev.at k e = some l) :
    e.loc = l :=
  Proofs.Semantics.Accept.IO.loc_of_at h

/-- An output of a local view is an output event of the trace. -/
theorem exists_out_of_mem_localView {k : K} {t : List (Ev K X I O C)} {b : O}
    (h : Loc.out b ∈ localView k t) : ∃ k', Ev.out k' b ∈ t :=
  Proofs.Semantics.Accept.IO.exists_out_of_mem_localView h

/-- An input of a local view is an input event of the trace. -/
theorem exists_inp_of_mem_localView {k : K} {t : List (Ev K X I O C)} {i : I}
    (h : Loc.inp i ∈ localView k t) : ∃ k', Ev.inp k' i ∈ t :=
  Proofs.Semantics.Accept.IO.exists_inp_of_mem_localView h

/-- A local view is a sublist of the trace's events. -/
theorem localView_sublist (k : K) (evs : List (Ev K X I O C)) :
    localView k evs <+ evs.map Ev.loc :=
  Proofs.Semantics.Accept.IO.localView_sublist k evs

end Provenance

/-! ## Scope assignment -/

section Assign

@[simp] theorem Tag.loc_enter (x : Option X) : (Tag.enter x : Tag X I O C).loc = .enter x := rfl
@[simp] theorem Tag.loc_inp (i : I) : (Tag.inp i : Tag X I O C).loc = .inp i := rfl
@[simp] theorem Tag.loc_out (o : O) : (Tag.out o : Tag X I O C).loc = .out o := rfl
@[simp] theorem Tag.loc_exit (c : Option C) : (Tag.exit c : Tag X I O C).loc = .exit c := rfl

omit [DecidableEq K] in
@[simp] theorem Ev.tag_enter (k : K) (x : Option X) :
    (Ev.enter k x : Ev K X I O C).tag = .enter x := rfl
omit [DecidableEq K] in
@[simp] theorem Ev.tag_inp (k : K) (i : I) : (Ev.inp k i : Ev K X I O C).tag = .inp i := rfl
omit [DecidableEq K] in
@[simp] theorem Ev.tag_out (k : K) (o : O) : (Ev.out k o : Ev K X I O C).tag = .out o := rfl
omit [DecidableEq K] in
@[simp] theorem Ev.tag_exit (k : K) (c : Option C) :
    (Ev.exit k c : Ev K X I O C).tag = .exit c := rfl

omit [DecidableEq K] in
/-- A scoped event's local event is the local event of its tag. -/
@[simp] theorem Ev.tag_loc (e : Ev K X I O C) : e.tag.loc = e.loc := by cases e <;> rfl

open scoped List

/-- Every assigned event comes from a tag of the list. -/
theorem tag_mem_of_mem_assign {st : List ℕ} {n : ℕ} {ts : List (Tag X I O C)}
    {e : Ev ℕ X I O C} (h : e ∈ assign st n ts) : e.tag ∈ ts :=
  Proofs.Semantics.Accept.IO.tag_mem_of_mem_assign h

/-- Assigned scopes are open scopes or fresh (at least the position counter). -/
theorem assign_scope (st : List ℕ) (n : ℕ) (ts : List (Tag X I O C)) :
    ∀ e ∈ assign st n ts, e.scope ∈ st ∨ n ≤ e.scope :=
  Proofs.Semantics.Accept.IO.assign_scope st n ts

/-- With no open scope, scopes below the position counter have empty views. -/
theorem localView_assign_lt {k n : ℕ} (hk : k < n) (ts : List (Tag X I O C)) :
    localView k (assign [] n ts) = [] :=
  Proofs.Semantics.Accept.IO.localView_assign_lt hk ts

/-- Tags before any `enter` (outside every invocation) are dropped. -/
theorem assign_nil_append {pre post : List (Tag X I O C)} (hpre : ∀ y, Tag.enter y ∉ pre)
    (n : ℕ) : assign [] n (pre ++ post) = assign [] (n + pre.length) post :=
  Proofs.Semantics.Accept.IO.assign_nil_append hpre n

/-- Scope assignment keeps (a sublist of) the tags, in order. -/
theorem map_loc_assign_sublist (st : List ℕ) (n : ℕ) (ts : List (Tag X I O C)) :
    (assign st n ts).map Ev.loc <+ ts.map Tag.loc :=
  Proofs.Semantics.Accept.IO.map_loc_assign_sublist st n ts

end Assign

end Silmaril.Accept.IO
