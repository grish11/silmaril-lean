module

public import Silmaril.Wasm.Game.IOAccept.Defs
public import Silmaril.Semantics.Accept.IO.Thms

/-!
# Traced I/O acceptance of core Wasm modules: proofs

* `calloutAt?_eq_some_iff`: `calloutAt?` computes `CalloutOf`;
* erasure: `toSession` (a traced session is a session) and `exists_of_session` (every session
  is traced, with some trace);
* provenance of tags: `exists_of_out`, `exists_of_inp` (each output and input tag comes from a
  reachable callout);
* scoped events back to tags: `out_mem_of_windows`, `out_mem_of_entryRun`,
  `inp_mem_of_windows`, `exists_out_of_mem_localView`, `evTag_mem_of_mem_assign`;
* scope facts: `openScan_eq` (flatness), `no_enter_of_inst`, `split` and `bracket_eq`
  (instantiation-phase tags are dropped by `bracket`).

New proofs.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.IOAccept

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept Silmaril.Accept.IO
  Silmaril.Wasm.Game.IOAccept

variable {X I O C : Type}

/-! ## Callouts -/

theorem calloutAt?_eq_some_iff {m : Module} {memAddr : Option Nat} {c : Config Nat}
    {o : Callout} : calloutAt? m memAddr c = some o ↔ CalloutOf m memAddr c o := by
  unfold calloutAt? CalloutOf
  constructor
  · intro h
    obtain ⟨⟨E, fa, hc, args⟩, hd, h'⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.1 h'
    exact ⟨E, fa, hc, hd, by simp [hi], rfl⟩
  · rintro ⟨E, fa, hc, hd, himp, hmem⟩
    obtain ⟨i, hi, he⟩ := Option.map_eq_some_iff.1 himp
    rw [hd]
    obtain ⟨imp, args, mem⟩ := o
    simp only at he hmem
    subst he hmem
    simp [hi, memOf]

/-! ## Tags of callouts and answers -/

theorem out_mem_callTags {R : Roles X I O C} {o : Callout} {b : O}
    (h : Tag.out b ∈ R.callTags o) : R.callOut o = some b := by
  simpa [Roles.callTags] using h

theorem inp_mem_callTags {R : Roles X I O C} {o : Callout} {i : I}
    (h : Tag.inp i ∈ R.callTags o) : R.callIn o = some i := by
  simpa [Roles.callTags] using h

theorem not_out_mem_answerTags {R : Roles X I O C} {o : Callout} {w : HostReply} {b : O} :
    Tag.out b ∉ R.answerTags o w := by
  simp [Roles.answerTags]

theorem inp_mem_answerTags {R : Roles X I O C} {o : Callout} {w : HostReply} {i : I}
    (h : Tag.inp i ∈ R.answerTags o w) : R.answerIn o w = some i := by
  simpa [Roles.answerTags] using h

theorem not_enter_mem_callTags {R : Roles X I O C} {o? : Option Callout} {y : Option X} :
    Tag.enter y ∉ o?.elim [] R.callTags := by
  cases o? <;> simp [Roles.callTags]

theorem not_enter_mem_answerTags {R : Roles X I O C} {o? : Option Callout} {w : HostReply}
    {y : Option X} : Tag.enter y ∉ o?.elim [] (fun o => R.answerTags o w) := by
  cases o? <;> simp [Roles.answerTags]

/-! ## Erasure -/

variable {P : Profile} {L : SEnv UImp} {m : Module} {memAddr : Option Nat} {R : Roles X I O C}
  {c₀ : Config Nat} {q₀ : L.S} {addrs : List Nat}

/-- A traced session is a session. -/
theorem toSession {p : Phase} {w : Bool} {x : Config Nat × L.S} {ts : List (Tag X I O C)}
    (h : TSession P L m memAddr R c₀ q₀ addrs p w x ts) :
    Session P L c₀ q₀ addrs p.started x := by
  induction h with
  | start => exact .start
  | internal _ st ih => exact .step ih (.internal st)
  | call _ _ ih => exact ih
  | answer _ hd ans ih => exact .step ih (.answer hd ans)
  | invoke _ _ fin ha ok ih => exact .invoke ih fin ha ok
  | ret _ _ ih => exact ih

/-- Every session is traced. -/
theorem exists_of_session {b : Bool} {x : Config Nat × L.S}
    (h : Session P L c₀ q₀ addrs b x) :
    ∃ (p : Phase) (w : Bool) (ts : List (Tag X I O C)), p.started = b ∧
      TSession P L m memAddr R c₀ q₀ addrs p w x ts := by
  induction h with
  | start => exact ⟨.inst, false, [], rfl, .start⟩
  | step _ st ih =>
    obtain ⟨p, w, ts, hp, h⟩ := ih
    cases st with
    | internal st => exact ⟨p, false, ts, hp, .internal h st⟩
    | answer hd ans =>
      cases w with
      | false => exact ⟨p, false, _, hp, .answer (.call h hd) hd ans⟩
      | true => exact ⟨p, false, _, hp, .answer h hd ans⟩
    | silent _ _ => exact ⟨p, w, ts, hp, h⟩
  | invoke _ fin ha ok ih =>
    obtain ⟨p, w, ts, rfl, h⟩ := ih
    cases p with
    | inst => exact ⟨.run, false, _, rfl, .invoke h (by decide) fin ha ok⟩
    | idle => exact ⟨.run, false, _, rfl, .invoke h (by decide) fin ha ok⟩
    | run =>
      obtain ⟨r, hr⟩ : ∃ r : Result, _ = r.toAdmin := fin
      exact ⟨.run, false, _, rfl, .invoke (.ret h hr) (by decide) ⟨r, hr⟩ ha ok⟩

/-! ## Provenance of tags -/

/-- Every output tag is the `callOut` of a callout at a reachable configuration. -/
theorem exists_of_out {p : Phase} {w : Bool} {x : Config Nat × L.S} {ts : List (Tag X I O C)}
    {b : O} (h : TSession P L m memAddr R c₀ q₀ addrs p w x ts) (hb : Tag.out b ∈ ts) :
    ∃ (b' : Bool) (c : Config Nat) (q : L.S) (o : Callout), Session P L c₀ q₀ addrs b' (c, q) ∧
      CalloutOf m memAddr c o ∧ R.callOut o = some b := by
  induction h with
  | start => simp at hb
  | internal _ _ ih => exact ih hb
  | @call p c q ts E fa hc args hs hd ih =>
    rcases List.mem_append.1 hb with hb | hb
    · exact ih hb
    · cases ho : calloutAt? m memAddr c with
      | none => simp [ho] at hb
      | some o =>
        rw [ho] at hb
        exact ⟨_, c, q, o, toSession hs, calloutAt?_eq_some_iff.1 ho, out_mem_callTags hb⟩
  | @answer p c q q' ts E fa hc args a hs hd ans ih =>
    rcases List.mem_append.1 hb with hb | hb
    · exact ih hb
    · cases ho : calloutAt? m memAddr c with
      | none => simp [ho] at hb
      | some o =>
        rw [ho] at hb
        exact absurd hb not_out_mem_answerTags
  | invoke _ _ _ _ _ ih => exact ih (by simpa using hb)
  | ret _ _ ih => exact ih (by simpa using hb)

/-- Every input tag is the `callIn` of a callout at a reachable configuration, or the
`answerIn` of an answer to it. -/
theorem exists_of_inp {p : Phase} {w : Bool} {x : Config Nat × L.S} {ts : List (Tag X I O C)}
    {i : I} (h : TSession P L m memAddr R c₀ q₀ addrs p w x ts) (hi : Tag.inp i ∈ ts) :
    ∃ (b' : Bool) (c : Config Nat) (q : L.S) (o : Callout), Session P L c₀ q₀ addrs b' (c, q) ∧
      CalloutOf m memAddr c o ∧ (R.callIn o = some i ∨ ∃ w, R.answerIn o w = some i) := by
  induction h with
  | start => simp at hi
  | internal _ _ ih => exact ih hi
  | @call p c q ts E fa hc args hs hd ih =>
    rcases List.mem_append.1 hi with hi | hi
    · exact ih hi
    · cases ho : calloutAt? m memAddr c with
      | none => simp [ho] at hi
      | some o =>
        rw [ho] at hi
        exact ⟨_, c, q, o, toSession hs, calloutAt?_eq_some_iff.1 ho,
          .inl (inp_mem_callTags hi)⟩
  | @answer p c q q' ts E fa hc args a hs hd ans ih =>
    rcases List.mem_append.1 hi with hi | hi
    · exact ih hi
    · cases ho : calloutAt? m memAddr c with
      | none => simp [ho] at hi
      | some o =>
        rw [ho] at hi
        exact ⟨_, c, q, o, toSession hs, calloutAt?_eq_some_iff.1 ho,
          .inr ⟨_, inp_mem_answerTags hi⟩⟩
  | invoke _ _ _ _ _ ih => exact ih (by simpa using hi)
  | ret _ _ ih => exact ih (by simpa using hi)

/-! ## Scoped events back to tags -/

theorem out_mem_of_collect {stop : Bool} {l : List (Loc X I O C)} {b : O}
    (h : b ∈ (collect stop l).1) : Loc.out b ∈ l := by
  induction l with
  | nil => simp [collect] at h
  | cons e l ih =>
    cases e with
    | out o =>
      simp only [collect, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)
    | exit c => simp [collect] at h
    | inp i =>
      cases stop with
      | true => simp [collect] at h
      | false => exact List.mem_cons_of_mem _ (ih (by simpa [collect] using h))
    | enter x => exact List.mem_cons_of_mem _ (ih (by simpa [collect] using h))

theorem out_mem_of_windows {l : List (Loc X I O C)} {r : Run I O C} {b : O}
    (hr : r ∈ windows l) (hb : b ∈ r.outputs) : Loc.out b ∈ l := by
  obtain ⟨pre, i, post, rfl, -, rfl⟩ := mem_windows.1 hr
  exact List.mem_append_right _ (List.mem_cons_of_mem _ (out_mem_of_collect hb))

theorem inp_mem_of_windows {l : List (Loc X I O C)} {r : Run I O C} (hr : r ∈ windows l) :
    Loc.inp r.input ∈ l := by
  obtain ⟨pre, i, post, rfl, -, rfl⟩ := mem_windows.1 hr
  simp

theorem out_mem_of_entryRun {l : List (Loc X I O C)} {r : Run X O C} {b : O}
    (hr : entryRun l = some r) (hb : b ∈ r.outputs) : Loc.out b ∈ l := by
  unfold entryRun at hr
  split at hr
  · cases hr
    exact List.mem_cons_of_mem _ (out_mem_of_collect hb)
  · cases hr

theorem loc_of_at {K : Type} [DecidableEq K] {k : K} {e : Ev K X I O C} {l : Loc X I O C}
    (h : Ev.at k e = some l) : e.loc = l := by
  unfold Ev.at at h
  split at h
  · exact Option.some.inj h
  · cases h

theorem exists_out_of_mem_localView {K : Type} [DecidableEq K] {k : K}
    {t : List (Ev K X I O C)} {b : O} (h : Loc.out b ∈ localView k t) : ∃ k', Ev.out k' b ∈ t := by
  obtain ⟨e, he, hk⟩ := List.mem_filterMap.1 h
  cases e with
  | out k' o =>
    have hl := loc_of_at hk
    simp only [Ev.loc] at hl
    cases hl
    exact ⟨k', he⟩
  | _ =>
    have hl := loc_of_at hk
    simp [Ev.loc] at hl

theorem exists_inp_of_mem_localView {K : Type} [DecidableEq K] {k : K}
    {t : List (Ev K X I O C)} {i : I} (h : Loc.inp i ∈ localView k t) : ∃ k', Ev.inp k' i ∈ t := by
  obtain ⟨e, he, hk⟩ := List.mem_filterMap.1 h
  cases e with
  | inp k' o =>
    have hl := loc_of_at hk
    simp only [Ev.loc] at hl
    cases hl
    exact ⟨k', he⟩
  | _ =>
    have hl := loc_of_at hk
    simp [Ev.loc] at hl

/-- The tag of a scoped event. -/
def evTag {K : Type} : Ev K X I O C → Tag X I O C
  | .enter _ x => .enter x
  | .inp _ i => .inp i
  | .out _ o => .out o
  | .exit _ c => .exit c

/-- Every event assigned by `assign` comes from a tag of the list. -/
theorem evTag_mem_of_mem_assign {st : List ℕ} {n : ℕ} {ts : List (Tag X I O C)}
    {e : Ev ℕ X I O C} (h : e ∈ assign st n ts) : evTag e ∈ ts := by
  induction ts generalizing st n with
  | nil => simp [assign] at h
  | cons t ts ih =>
    cases t with
    | enter x =>
      simp only [assign, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)
    | inp i =>
      cases st with
      | nil => exact List.mem_cons_of_mem _ (ih (by simpa [assign] using h))
      | cons k st =>
        simp only [assign, List.mem_cons] at h
        rcases h with rfl | h
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih h)
    | out o =>
      cases st with
      | nil => exact List.mem_cons_of_mem _ (ih (by simpa [assign] using h))
      | cons k st =>
        simp only [assign, List.mem_cons] at h
        rcases h with rfl | h
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih h)
    | exit c =>
      cases st with
      | nil => exact List.mem_cons_of_mem _ (ih (by simpa [assign] using h))
      | cons k st =>
        simp only [assign, List.mem_cons] at h
        rcases h with rfl | h
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih h)

/-! ## Scope facts -/

theorem openScan_append (b : Bool) (ts us : List (Tag X I O C)) :
    openScan b (ts ++ us) = (openScan b ts).bind (openScan · us) := by
  induction ts generalizing b with
  | nil => simp [openScan]
  | cons t ts ih => cases t <;> cases b <;> simp [openScan, ih]

theorem openScan_map_inp (b : Bool) (l : List I) :
    openScan b (l.map (Tag.inp (X := X) (O := O) (C := C))) = some b := by
  induction l <;> simp_all [openScan]

theorem openScan_map_out (b : Bool) (l : List O) :
    openScan b (l.map (Tag.out (X := X) (I := I) (C := C))) = some b := by
  induction l <;> simp_all [openScan]

theorem openScan_callTags (b : Bool) (o? : Option Callout) :
    openScan b (o?.elim [] R.callTags) = some b := by
  cases o? with
  | none => rfl
  | some o => simp [Roles.callTags, openScan_append, openScan_map_inp, openScan_map_out]

theorem openScan_answerTags (b : Bool) (o? : Option Callout) (w : HostReply) :
    openScan b (o?.elim [] fun o => R.answerTags o w) = some b := by
  cases o? with
  | none => rfl
  | some o => simp [Roles.answerTags, openScan_map_inp]

/-- **Traced sessions are flat**: `enter` and `exit` alternate, and the scan ends inside an
invocation exactly in phase `run`. -/
theorem openScan_eq {p : Phase} {w : Bool} {x : Config Nat × L.S} {ts : List (Tag X I O C)}
    (h : TSession P L m memAddr R c₀ q₀ addrs p w x ts) :
    openScan false ts = some (decide (p = .run)) := by
  induction h with
  | start => rfl
  | internal _ _ ih => exact ih
  | call _ _ ih => simp [openScan_append, ih, openScan_callTags]
  | answer _ _ _ ih => simp [openScan_append, ih, openScan_answerTags]
  | invoke _ hp _ _ _ ih => simp [openScan_append, ih, hp, openScan]
  | ret _ _ ih => simp [openScan_append, ih, openScan]

/-- No `enter` is tagged during instantiation. -/
theorem no_enter_of_inst {p : Phase} {w : Bool} {x : Config Nat × L.S}
    {ts : List (Tag X I O C)} (h : TSession P L m memAddr R c₀ q₀ addrs p w x ts)
    (hp : p = .inst) (y : Option X) : Tag.enter y ∉ ts := by
  induction h with
  | start => simp
  | internal _ _ ih => exact ih hp
  | call _ _ ih =>
    simp only [List.mem_append, not_or]
    exact ⟨ih hp, not_enter_mem_callTags⟩
  | answer _ _ _ ih =>
    simp only [List.mem_append, not_or]
    exact ⟨ih hp, not_enter_mem_answerTags⟩
  | invoke => cases hp
  | ret => cases hp

/-- **The shape of a traced session**: a prefix without `enter` (the instantiation phase),
then nothing (still instantiating) or an `enter`. -/
theorem split {p : Phase} {w : Bool} {x : Config Nat × L.S} {ts : List (Tag X I O C)}
    (h : TSession P L m memAddr R c₀ q₀ addrs p w x ts) :
    ∃ pre post, ts = pre ++ post ∧ (∀ y, Tag.enter y ∉ pre) ∧
      (p = .inst ∧ post = [] ∨ p ≠ .inst ∧ ∃ y rest, post = Tag.enter y :: rest) := by
  induction h with
  | start => exact ⟨[], [], rfl, by simp, .inl ⟨rfl, rfl⟩⟩
  | internal _ _ ih => exact ih
  | call _ _ ih =>
    obtain ⟨pre, post, rfl, hpre, ⟨hp, rfl⟩ | ⟨hp, y, rest, rfl⟩⟩ := ih
    · refine ⟨_, [], (List.append_nil _).symm, fun y => ?_, .inl ⟨hp, rfl⟩⟩
      simp only [List.append_nil, List.mem_append, not_or]
      exact ⟨hpre y, not_enter_mem_callTags⟩
    · exact ⟨pre, _, List.append_assoc _ _ _, hpre, .inr ⟨hp, y, _, rfl⟩⟩
  | answer _ _ _ ih =>
    obtain ⟨pre, post, rfl, hpre, ⟨hp, rfl⟩ | ⟨hp, y, rest, rfl⟩⟩ := ih
    · refine ⟨_, [], (List.append_nil _).symm, fun y => ?_, .inl ⟨hp, rfl⟩⟩
      simp only [List.append_nil, List.mem_append, not_or]
      exact ⟨hpre y, not_enter_mem_answerTags⟩
    · exact ⟨pre, _, List.append_assoc _ _ _, hpre, .inr ⟨hp, y, _, rfl⟩⟩
  | @invoke p w c q ts a args _ _ _ _ _ ih =>
    obtain ⟨pre, post, rfl, hpre, ⟨hp, rfl⟩ | ⟨hp, y, rest, rfl⟩⟩ := ih
    · exact ⟨pre, [.enter (R.entry a args)], by rw [List.append_nil], hpre,
        .inr ⟨by decide, _, [], rfl⟩⟩
    · exact ⟨pre, _, List.append_assoc _ _ _, hpre, .inr ⟨by decide, y, _, rfl⟩⟩
  | ret _ _ ih =>
    obtain ⟨pre, post, rfl, hpre, ⟨hp, -⟩ | ⟨hp, y, rest, rfl⟩⟩ := ih
    · cases hp
    · exact ⟨pre, _, List.append_assoc _ _ _, hpre, .inr ⟨by decide, y, _, rfl⟩⟩

/-- Tags before any `enter` are dropped by the scope assignment. -/
theorem assign_nil_append {pre post : List (Tag X I O C)} (hpre : ∀ y, Tag.enter y ∉ pre)
    (n : ℕ) : assign [] n (pre ++ post) = assign [] (n + pre.length) post := by
  induction pre generalizing n with
  | nil => rfl
  | cons t pre ih =>
    have hpre' : ∀ y, Tag.enter y ∉ pre := fun y hy => hpre y (List.mem_cons_of_mem _ hy)
    cases t with
    | enter y => exact absurd List.mem_cons_self (hpre y)
    | _ =>
      simp only [List.cons_append, assign, ih hpre', List.length_cons]
      congr 1
      omega

/-- The scope assignment of a traced session drops its instantiation-phase prefix. -/
theorem bracket_eq {p : Phase} {w : Bool} {x : Config Nat × L.S} {ts : List (Tag X I O C)}
    (h : TSession P L m memAddr R c₀ q₀ addrs p w x ts) :
    ∃ pre post, ts = pre ++ post ∧ (∀ y, Tag.enter y ∉ pre) ∧
      bracket ts = assign [] pre.length post ∧ (p = .inst → post = []) := by
  obtain ⟨pre, post, rfl, hpre, hpost⟩ := split h
  refine ⟨pre, post, rfl, hpre, ?_, fun hp => ?_⟩
  · simpa [bracket] using assign_nil_append (post := post) hpre 0
  · rcases hpost with ⟨-, h⟩ | ⟨hn, -⟩
    · exact h
    · exact absurd hp hn

/-! ## Modules -/

variable {Envs : Store Nat → SEnv UImp → Prop} {memIdx : Nat}

/-- An output tag of a module's trace is the `callOut` of one of its reachable callouts. -/
theorem exists_callout_of_out {ts : List (Tag X I O C)} {b : O}
    (hts : ts ∈ tagTraces P Envs memIdx m R) (hb : Tag.out b ∈ ts) :
    ∃ o ∈ Callouts P Envs memIdx m, R.callOut o = some b := by
  obtain ⟨mt, Is, c₀, hI, L, q₀, hL, p, w, x, h⟩ := hts
  obtain ⟨b', c, q, o, hs, ho, hob⟩ := exists_of_out h hb
  exact ⟨o, ⟨mt, Is, c₀, hI, L, q₀, hL, b', c, q, hs, ho⟩, hob⟩

/-- An input tag of a module's trace is read off one of its reachable callouts. -/
theorem exists_callout_of_inp {ts : List (Tag X I O C)} {i : I}
    (hts : ts ∈ tagTraces P Envs memIdx m R) (hi : Tag.inp i ∈ ts) :
    ∃ o ∈ Callouts P Envs memIdx m, R.callIn o = some i ∨ ∃ w, R.answerIn o w = some i := by
  obtain ⟨mt, Is, c₀, hI, L, q₀, hL, p, w, x, h⟩ := hts
  obtain ⟨b', c, q, o, hs, ho, hoi⟩ := exists_of_inp h hi
  exact ⟨o, ⟨mt, Is, c₀, hI, L, q₀, hL, b', c, q, hs, ho⟩, hoi⟩

/-- Every output of an input-window run is the `callOut` of a reachable callout. -/
theorem exists_callout_of_mem_ioRuns {r : Run I O C} {b : O}
    (hr : r ∈ ioRuns P Envs memIdx m R) (hb : b ∈ r.outputs) :
    ∃ o ∈ Callouts P Envs memIdx m, R.callOut o = some b := by
  obtain ⟨_, ⟨ts, hts, rfl⟩, hr⟩ := hr
  obtain ⟨k, hk⟩ := mem_inputRuns.1 hr
  obtain ⟨k', hk'⟩ := exists_out_of_mem_localView (out_mem_of_windows hk hb)
  exact exists_callout_of_out hts (evTag_mem_of_mem_assign (e := .out k' b) hk')

/-- Every output of an entry run is the `callOut` of a reachable callout. -/
theorem exists_callout_of_mem_entryIORuns {r : Run X O C} {b : O}
    (hr : r ∈ entryIORuns P Envs memIdx m R) (hb : b ∈ r.outputs) :
    ∃ o ∈ Callouts P Envs memIdx m, R.callOut o = some b := by
  obtain ⟨_, ⟨ts, hts, rfl⟩, hr⟩ := hr
  obtain ⟨k, hk⟩ := mem_entryRuns.1 hr
  obtain ⟨k', hk'⟩ := exists_out_of_mem_localView (out_mem_of_entryRun hk hb)
  exact exists_callout_of_out hts (evTag_mem_of_mem_assign (e := .out k' b) hk')

/-- The input of an input-window run is read off a reachable callout. -/
theorem exists_callout_of_input_ioRuns {r : Run I O C} (hr : r ∈ ioRuns P Envs memIdx m R) :
    ∃ o ∈ Callouts P Envs memIdx m,
      R.callIn o = some r.input ∨ ∃ w, R.answerIn o w = some r.input := by
  obtain ⟨_, ⟨ts, hts, rfl⟩, hr⟩ := hr
  obtain ⟨k, hk⟩ := mem_inputRuns.1 hr
  obtain ⟨k', hk'⟩ := exists_inp_of_mem_localView (inp_mem_of_windows hk)
  exact exists_callout_of_inp hts (evTag_mem_of_mem_assign (e := .inp k' r.input) hk')

/-- The callouts of a module are those reachable in its traced sessions. -/
theorem callouts_eq_traced :
    Callouts P Envs memIdx m = {o | ∃ (mt : CModuleType) (Is : ScalarInstance) (c₀ : Config Nat),
      IsSpecInstance m mt Is c₀ ∧ ∃ (L : SEnv UImp) (q₀ : L.S), Envs Is.store L ∧
      ∃ (p : Phase) (w : Bool) (c : Config Nat) (q : L.S) (ts : List (Tag X I O C)),
        TSession P L m c₀.frame.module.mems[memIdx]? R c₀ q₀ Is.addrs p w (c, q) ts ∧
        CalloutOf m c₀.frame.module.mems[memIdx]? c o} := by
  ext o
  constructor
  · rintro ⟨mt, Is, c₀, hI, L, q₀, hL, b, c, q, hs, ho⟩
    obtain ⟨p, w, ts, -, h⟩ := exists_of_session (m := m) (R := R)
      (memAddr := c₀.frame.module.mems[memIdx]?) hs
    exact ⟨mt, Is, c₀, hI, L, q₀, hL, p, w, c, q, ts, h, ho⟩
  · rintro ⟨mt, Is, c₀, hI, L, q₀, hL, p, w, c, q, ts, h, ho⟩
    exact ⟨mt, Is, c₀, hI, L, q₀, hL, _, c, q, toSession h, ho⟩

end Silmaril.Proofs.Wasm.Game.IOAccept
