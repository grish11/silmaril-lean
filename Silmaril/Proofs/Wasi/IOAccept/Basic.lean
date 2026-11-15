module

public import Silmaril.Wasi.IOAccept.Defs
public import Silmaril.Semantics.Accept.IO.Thms

/-! # Proofs: relational I/O acceptance of component traces

Proofs of `Silmaril.Wasi.IOAccept.Thms`: legal plays are `Shallow`, the scopes `bracket` assigns
to a `Shallow` tag list are its `blocks`, the blocks of decoded named traces are the decoded
call blocks (`wblocks`), and decoded runs are read off ordered pairs of events of the trace.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasi.IOAccept

open Silmaril.Games Silmaril.Accept.IO Silmaril.Wasi Silmaril.Wasi.IOAccept
open Silmaril.Wasm.Component (Val)
open scoped List

variable {X I O C : Type}

/-! ## Legal plays are shallow -/

/-- Inside an export call. -/
def busy {E F : Sig.{0}} : Pos E F → Bool
  | .idle => false
  | _ => true

theorem shallow_of_path (ρ : Roles X I O C) {Im Ex : Set FnName}
    {x z : Pos (nsig Im) (nsig Ex)} {s : List (Move (nsig Im) (nsig Ex))} (h : Path x s z) :
    Shallow (busy x) ((wtrace s).filterMap (tag ρ)) := by
  induction h with
  | nil => exact .nil _
  | cons hst _ ih =>
    simp only [wtrace, List.map_cons, List.filterMap_cons] at ih ⊢
    cases hst with
    | ask q => exact .enter _ ih
    | call q m =>
      simp only [wev, tag]
      rcases ρ.callOut m.1.1 m.2 with _ | o
      · rcases ρ.callIn m.1.1 m.2 with _ | i
        · exact ih
        · exact .inp i ih
      · exact .out o ih
    | reply q m n =>
      rcases n with _ | r
      · exact ih
      · simp only [wev, tag]
        rcases ρ.answerIn m.1.1 m.2 r with _ | i
        · exact ih
        · exact .inp i ih
    | ret q r =>
      rcases r with _ | r
      · exact .exit _ ih
      · exact .exit _ ih

theorem shallow_of_legal (ρ : Roles X I O C) {Im Ex : Set FnName}
    {s : List (Move (nsig Im) (nsig Ex))} (hs : Legal s) :
    Shallow false ((wtrace s).filterMap (tag ρ)) :=
  let ⟨_, h⟩ := hs; shallow_of_path ρ h

/-! ## Scope assignment of shallow tag lists -/

/-- A tag at the scope `k`. -/
def atScope (k : ℕ) : Tag X I O C → Ev ℕ X I O C
  | .enter x => .enter k x
  | .inp i => .inp k i
  | .out o => .out k o
  | .exit c => .exit k c

theorem assign_body {body : List (Tag X I O C)} (hb : ∀ t ∈ body, IsBody t) (k : ℕ)
    (st : List ℕ) (n : ℕ) (rest : List (Tag X I O C)) :
    assign (k :: st) n (body ++ rest) =
      body.map (atScope k) ++ assign (k :: st) (n + body.length) rest := by
  induction body generalizing n with
  | nil => simp
  | cons t body ih =>
    have hb' : ∀ t ∈ body, IsBody t := fun t h => hb t (List.mem_cons_of_mem _ h)
    have ht := hb t List.mem_cons_self
    have hn : n + (body.length + 1) = n + 1 + body.length := by omega
    cases t with
    | enter x => exact ht.elim
    | exit c => exact ht.elim
    | inp i =>
      simp only [List.cons_append, assign, List.map_cons, List.length_cons, ih hb', hn]
      rfl
    | out o =>
      simp only [List.cons_append, assign, List.map_cons, List.length_cons, ih hb', hn]
      rfl

theorem localView_map_scoped (j k : ℕ) (l : List (Tag X I O C)) :
    localView j (l.map (atScope k)) = if j = k then l.map tagLoc else [] := by
  induction l with
  | nil => simp [localView]
  | cons t l ih =>
    have h₁ : (atScope k t).scope = k := by cases t <;> rfl
    have h₂ : (atScope k t).loc = tagLoc t := by cases t <;> rfl
    by_cases hjk : j = k
    · subst hjk
      rw [List.map_cons, localView_cons_of_eq _ h₁, ih]
      simp [h₂]
    · rw [List.map_cons, localView_cons_of_ne _ (by rw [h₁]; exact Ne.symm hjk), ih]
      simp [hjk]

theorem shallow_true_split {l : List (Tag X I O C)} (h : Shallow true l) :
    ∃ body, (∀ t ∈ body, IsBody t) ∧
      (l = body ∨ ∃ c rest, l = body ++ .exit c :: rest ∧ Shallow false rest) := by
  induction l with
  | nil => exact ⟨[], by simp, .inl rfl⟩
  | cons t l ih =>
    cases h with
    | inp i h =>
      obtain ⟨body, hb, hl⟩ := ih h
      refine ⟨.inp i :: body, ?_, ?_⟩
      · simpa [IsBody] using hb
      · rcases hl with rfl | ⟨c, rest, rfl, hr⟩
        · exact .inl rfl
        · exact .inr ⟨c, rest, rfl, hr⟩
    | out o h =>
      obtain ⟨body, hb, hl⟩ := ih h
      refine ⟨.out o :: body, ?_, ?_⟩
      · simpa [IsBody] using hb
      · rcases hl with rfl | ⟨c, rest, rfl, hr⟩
        · exact .inl rfl
        · exact .inr ⟨c, rest, rfl, hr⟩
    | exit c h => exact ⟨[], by simp, .inr ⟨c, l, rfl, h⟩⟩

theorem seg_body {body : List (Tag X I O C)} (hb : ∀ t ∈ body, IsBody t)
    (rest : List (Tag X I O C)) : seg (body ++ rest) = body.map tagLoc ++ seg rest := by
  induction body with
  | nil => rfl
  | cons t body ih =>
    have ht := hb t List.mem_cons_self
    rw [List.cons_append, List.map_cons, List.cons_append,
      ← ih fun t h => hb t (List.mem_cons_of_mem _ h)]
    cases t with
    | enter x => exact ht.elim
    | exit c => exact ht.elim
    | inp i => rfl
    | out o => rfl

theorem blocks_body {body : List (Tag X I O C)} (hb : ∀ t ∈ body, IsBody t)
    (rest : List (Tag X I O C)) : blocks (body ++ rest) = blocks rest := by
  induction body with
  | nil => rfl
  | cons t body ih =>
    have ht := hb t List.mem_cons_self
    rw [List.cons_append, ← ih fun t h => hb t (List.mem_cons_of_mem _ h)]
    cases t with
    | enter x => exact ht.elim
    | exit c => exact ht.elim
    | inp i => rfl
    | out o => rfl

theorem seg_of_shallow {l : List (Tag X I O C)} (h : Shallow false l) : seg l = [] := by
  cases h <;> rfl

theorem ne_nil_of_mem_blocks {ts : List (Tag X I O C)} {l : List (Loc X I O C)}
    (h : l ∈ blocks ts) : l ≠ [] := by
  induction ts with
  | nil => simp [blocks] at h
  | cons t ts ih =>
    cases t with
    | enter x =>
      rcases List.mem_cons.1 h with rfl | h
      · simp
      · exact ih h
    | inp _ => exact ih h
    | out _ => exact ih h
    | exit _ => exact ih h

theorem assign_block (x : Option X) {body : List (Tag X I O C)} (hb : ∀ t ∈ body, IsBody t)
    (c : Option C) (rest : List (Tag X I O C)) (n : ℕ) :
    assign [] n (.enter x :: (body ++ .exit c :: rest)) =
      (Tag.enter x :: (body ++ [Tag.exit c])).map (atScope n) ++
        assign [] (n + 1 + body.length + 1) rest := by
  simp only [assign, assign_body hb]
  simp [atScope]

theorem assign_open (x : Option X) {body : List (Tag X I O C)} (hb : ∀ t ∈ body, IsBody t)
    (n : ℕ) : assign [] n (.enter x :: body) = (Tag.enter x :: body).map (atScope n) := by
  have := assign_body hb n [] (n + 1) []
  simp only [List.append_nil] at this
  simp only [assign, this]
  simp [atScope]

/-- **The scopes of a shallow tag list are its blocks.** -/
theorem views_of_shallow (ts : List (Tag X I O C)) (h : Shallow false ts) (n : ℕ) :
    (∀ k, localView k (assign [] n ts) = [] ∨ localView k (assign [] n ts) ∈ blocks ts) ∧
      (∀ l ∈ blocks ts, ∃ k, localView k (assign [] n ts) = l) := by
  cases h with
  | nil => exact ⟨fun _ => .inl rfl, by simp [blocks]⟩
  | @enter x l hl =>
    obtain ⟨body, hb, hl' | ⟨c, rest, hl', hr⟩⟩ := shallow_true_split hl <;> subst l
    · have hbl : blocks (.enter x :: body) = [.enter x :: body.map tagLoc] := by
        have h₁ := seg_body hb []
        have h₂ := blocks_body hb []
        simp only [List.append_nil] at h₁ h₂
        simp [blocks, h₁, h₂, seg, blocks]
      rw [hbl, assign_open x hb]
      refine ⟨fun k => ?_, fun l hl => ⟨n, ?_⟩⟩
      · rw [localView_map_scoped]
        split_ifs
        · exact .inr (by simp [tagLoc])
        · exact .inl rfl
      · rw [List.mem_singleton.1 hl, localView_map_scoped]
        simp [tagLoc]
    · have ih := views_of_shallow rest hr (n + 1 + body.length + 1)
      have hbl : blocks (.enter x :: (body ++ .exit c :: rest)) =
          (.enter x :: (body.map tagLoc ++ [.exit c])) :: blocks rest := by
        simp only [blocks, seg_body hb, blocks_body hb]
        simp [seg, seg_of_shallow hr, tagLoc]
      have hlt : n < n + 1 + body.length + 1 := by omega
      rw [hbl, assign_block x hb]
      refine ⟨fun k => ?_, fun l hl => ?_⟩
      · rw [localView, List.filterMap_append, ← localView, ← localView, localView_map_scoped]
        split_ifs with hk
        · subst hk
          rw [localView_assign_lt hlt]
          exact .inr (by simp [tagLoc])
        · rcases ih.1 k with h | h
          · exact .inl (by simpa using h)
          · exact .inr (List.mem_cons_of_mem _ (by simpa using h))
      · rcases List.mem_cons.1 hl with rfl | hl
        · refine ⟨n, ?_⟩
          rw [localView, List.filterMap_append, ← localView, ← localView, localView_map_scoped,
            localView_assign_lt hlt]
          simp [tagLoc]
        · obtain ⟨k, hk⟩ := ih.2 l hl
          have hkn : k ≠ n := by
            rintro rfl
            rw [localView_assign_lt hlt] at hk
            exact ne_nil_of_mem_blocks hl hk.symm
          refine ⟨k, ?_⟩
          rw [localView, List.filterMap_append, ← localView, ← localView, localView_map_scoped,
            ite_eq_right_iff.2 (fun h => absurd h hkn), hk, List.nil_append]
termination_by ts.length
decreasing_by subst_vars; simp only [List.length_cons, List.length_append]; omega

/-! ## Blocks of decoded named traces -/

theorem tag_call (ρ : Roles X I O C) {e : WEv} (he : isCall e = true) :
    ∃ x, tag ρ e = some (.enter x) := by
  cases e <;> simp_all [isCall, tag]

theorem tag_not_call (ρ : Roles X I O C) {e : WEv} (he : isCall e = false) :
    tag ρ e = none ∨ ∃ g, tag ρ e = some g ∧ ∀ x, g ≠ .enter x := by
  cases e with
  | call f a => simp [isCall] at he
  | ret f a r => rcases r with _ | r <;> simp [tag]
  | req f a =>
    simp only [tag]
    rcases ρ.callOut f a with _ | o
    · rcases ρ.callIn f a with _ | i <;> simp
    · simp
  | imp f a r =>
    rcases r with _ | r
    · simp [tag]
    · simp only [tag]
      rcases ρ.answerIn f a r with _ | i <;> simp

theorem seg_cons_of_ne {g : Tag X I O C} (hg : ∀ x, g ≠ .enter x) (ts : List (Tag X I O C)) :
    seg (g :: ts) = tagLoc g :: seg ts := by
  cases g <;> simp_all [seg]

theorem blocks_cons_of_ne {g : Tag X I O C} (hg : ∀ x, g ≠ .enter x)
    (ts : List (Tag X I O C)) : blocks (g :: ts) = blocks ts := by
  cases g <;> simp_all [blocks]

theorem seg_filterMap (ρ : Roles X I O C) (t : List WEv) :
    seg (t.filterMap (tag ρ)) = (wseg t).filterMap (locOf ρ) := by
  induction t with
  | nil => rfl
  | cons e t ih =>
    cases hc : isCall e
    · simp only [wseg, hc, Bool.false_eq_true, ite_false, List.filterMap_cons, locOf]
      rcases tag_not_call ρ hc with h | ⟨g, h, hg⟩
      · simpa [h] using ih
      · simp only [h, Option.map_some, seg_cons_of_ne hg, ih]
    · obtain ⟨x, h⟩ := tag_call ρ hc
      simp [wseg, hc, h, seg]

theorem blocks_filterMap (ρ : Roles X I O C) (t : List WEv) :
    blocks (t.filterMap (tag ρ)) = (wblocks t).map (·.filterMap (locOf ρ)) := by
  induction t with
  | nil => rfl
  | cons e t ih =>
    cases hc : isCall e
    · simp only [wblocks, hc, Bool.false_eq_true, ite_false, List.filterMap_cons]
      rcases tag_not_call ρ hc with h | ⟨g, h, hg⟩
      · simpa [h] using ih
      · simp only [h, blocks_cons_of_ne hg, ih]
    · obtain ⟨x, h⟩ := tag_call ρ hc
      simp only [wblocks, hc, ite_true, List.filterMap_cons, h, blocks, ih, List.map_cons,
        seg_filterMap]
      simp [locOf, h, tagLoc]

/-- **The runs of a legal play are the windows of its call blocks.** -/
theorem mem_inputRuns_decode {Im Ex : Set FnName} {s : List (Move (nsig Im) (nsig Ex))}
    (hs : Legal s) (ρ : Roles X I O C) (r : Run I O C) :
    r ∈ inputRuns (decode (tag ρ) (wtrace s)) ↔
      ∃ b ∈ wblocks (wtrace s), r ∈ windows (b.filterMap (locOf ρ)) := by
  have M := views_of_shallow _ (shallow_of_legal ρ hs) 0
  rw [blocks_filterMap] at M
  rw [mem_inputRuns]
  constructor
  · rintro ⟨k, hk⟩
    rcases M.1 k with h | h
    · rw [decode, bracket, h] at hk
      simp [windows] at hk
    · obtain ⟨b, hb, he⟩ := List.mem_map.1 h
      exact ⟨b, hb, by rw [he]; exact hk⟩
  · rintro ⟨b, hb, hr⟩
    obtain ⟨k, hk⟩ := M.2 _ (List.mem_map_of_mem hb)
    exact ⟨k, by rw [decode, bracket, hk]; exact hr⟩

/-- **The entry runs of a legal play are those of its call blocks.** -/
theorem mem_entryRuns_decode {Im Ex : Set FnName} {s : List (Move (nsig Im) (nsig Ex))}
    (hs : Legal s) (ρ : Roles X I O C) (r : Run X O C) :
    r ∈ entryRuns (decode (tag ρ) (wtrace s)) ↔
      ∃ b ∈ wblocks (wtrace s), entryRun (b.filterMap (locOf ρ)) = some r := by
  have M := views_of_shallow _ (shallow_of_legal ρ hs) 0
  rw [blocks_filterMap] at M
  rw [mem_entryRuns]
  constructor
  · rintro ⟨k, hk⟩
    rcases M.1 k with h | h
    · rw [decode, bracket, h] at hk
      simp [entryRun] at hk
    · obtain ⟨b, hb, he⟩ := List.mem_map.1 h
      exact ⟨b, hb, by rw [he]; exact hk⟩
  · rintro ⟨b, hb, hr⟩
    obtain ⟨k, hk⟩ := M.2 _ (List.mem_map_of_mem hb)
    exact ⟨k, by rw [decode, bracket, hk]; exact hr⟩

/-! ## No other export event inside an export call -/

theorem path_lower {Im Ex : Set FnName} {q : (nsig Ex).Op} :
    ∀ {x z : Pos (nsig Im) (nsig Ex)} {s : List (Move (nsig Im) (nsig Ex))},
      (x = .run q ∨ ∃ m, x = .wait q m) → Path x s z → (∀ m ∈ s, m.isLeft) →
      (z = .run q ∨ ∃ m, z = .wait q m)
  | _, _, _, hx, .nil _, _ => hx
  | _, _, _, hx, .cons hst hp, hs => by
    refine path_lower ?_ hp fun m hm => hs m (List.mem_cons_of_mem _ hm)
    have h₀ := hs _ List.mem_cons_self
    rcases hx with rfl | ⟨m, rfl⟩ <;> cases hst <;> simp_all

theorem isExp_wev {Im Ex : Set FnName} (m : Move (nsig Im) (nsig Ex)) :
    (wev m).isExp = m.isRight := by
  rcases m with (_ | _) | (_ | _) <;> rfl

/-- **After an export call, the next export event is the return (or trap) of that call.** -/
theorem ret_after_call {Im Ex : Set FnName} {s : List (Move (nsig Im) (nsig Ex))}
    (hs : Legal s) {u v w : List WEv} {f : FnName} {a : List Val} {e : WEv}
    (h : wtrace s = u ++ .call f a :: (v ++ e :: w)) (hv : ∀ e' ∈ v, e'.isExp = false)
    (he : e.isExp = true) : ∃ r, e = .ret f a r := by
  obtain ⟨y, hy⟩ := hs
  obtain ⟨s₁, s₂, rfl, h₁, h₂⟩ := List.map_eq_append_iff.1 h
  obtain ⟨m, s₂, rfl, hm, h₂⟩ := List.map_eq_cons_iff.1 h₂
  obtain ⟨s₃, s₄, rfl, h₃, h₄⟩ := List.map_eq_append_iff.1 h₂
  obtain ⟨m', s₅, rfl, hm', -⟩ := List.map_eq_cons_iff.1 h₄
  obtain ⟨x₁, -, hp⟩ := Path.of_append hy
  cases hp with
  | cons hst hp =>
    rcases m with (_ | _) | (_ | q)
    · cases hm
    · cases hm
    · cases hm
      cases hst
      obtain ⟨x₂, hp₃, hp⟩ := Path.of_append hp
      have hl : ∀ m ∈ s₃, m.isLeft := fun m hm => by
        have := hv _ (by rw [← h₃]; exact List.mem_map_of_mem hm)
        rw [isExp_wev] at this
        rcases m with _ | _ <;> simp_all
      have hx₂ := path_lower (.inl rfl) hp₃ hl
      cases hp with
      | cons hst' _ =>
        rw [← hm', isExp_wev] at he
        rcases hx₂ with rfl | ⟨m, rfl⟩ <;> cases hst' <;> simp_all [wev]
        exact ⟨_, h₄.1.symm⟩
    · cases hm

/-! ## Runs are read off ordered pairs of events -/

theorem localView_decode_sublist (ρ : Roles X I O C) (k : ℕ) (t : List WEv) :
    localView k (decode (tag ρ) t) <+ t.filterMap (locOf ρ) := by
  refine (localView_sublist k _).trans ?_
  have := map_loc_assign_sublist [] 0 (t.filterMap (tag ρ))
  rwa [List.map_filterMap] at this

theorem pair_of_sublist_filterMap {α β : Type} {g : α → Option β} {x y : β} :
    ∀ {t : List α}, [x, y] <+ t.filterMap g →
      ∃ e₁ e₂, [e₁, e₂] <+ t ∧ g e₁ = some x ∧ g e₂ = some y
  | [], h => by simp at h
  | e :: t, h => by
    rw [List.filterMap_cons] at h
    split at h
    · obtain ⟨a, b, h₁, h₂, h₃⟩ := pair_of_sublist_filterMap h
      exact ⟨a, b, h₁.cons _, h₂, h₃⟩
    · rename_i z hz
      rcases List.sublist_cons_iff.1 h with h | ⟨r, hr, h⟩
      · obtain ⟨a, b, h₁, h₂, h₃⟩ := pair_of_sublist_filterMap h
        exact ⟨a, b, h₁.cons _, h₂, h₃⟩
      · obtain ⟨rfl, rfl⟩ := List.cons.inj hr
        obtain ⟨e₂, he₂, hg⟩ := List.mem_filterMap.1 (List.singleton_sublist.1 h)
        exact ⟨e, e₂, (List.singleton_sublist.2 he₂).cons_cons _, hz, hg⟩

/-- **Triggering is sound**: an output of a decoded run comes from an output event after the
input event that started the run. -/
theorem triggers_sound (ρ : Roles X I O C) {t : List WEv} {r : Run I O C}
    (hr : r ∈ inputRuns (decode (tag ρ) t)) {b : O} (hb : b ∈ r.outputs) :
    ∃ e₁ e₂, [e₁, e₂] <+ t ∧ locOf ρ e₁ = some (.inp r.input) ∧
      locOf ρ e₂ = some (.out b) := by
  obtain ⟨k, hk⟩ := mem_inputRuns.1 hr
  obtain ⟨post, hpost, ho, -⟩ := sublist_of_windows hk
  rw [ho] at hb
  have h : [Loc.inp r.input, .out b] <+ t.filterMap (locOf ρ) :=
    (List.Sublist.cons_cons _ (List.singleton_sublist.2 (out_mem_of_collect hb))).trans
      (hpost.trans (localView_decode_sublist ρ k t))
  exact pair_of_sublist_filterMap h

/-- **Results are sound**: the result of a decoded run comes from a return event after the
input event that started the run. -/
theorem result_sound (ρ : Roles X I O C) {t : List WEv} {r : Run I O C}
    (hr : r ∈ inputRuns (decode (tag ρ) t)) {c : C} (hc : r.result = some c) :
    ∃ e₁ e₂, [e₁, e₂] <+ t ∧ locOf ρ e₁ = some (.inp r.input) ∧
      locOf ρ e₂ = some (.exit (some c)) := by
  obtain ⟨k, hk⟩ := mem_inputRuns.1 hr
  obtain ⟨post, hpost, -, hres⟩ := sublist_of_windows hk
  rw [hres] at hc
  have h : [Loc.inp r.input, .exit (some c)] <+ t.filterMap (locOf ρ) :=
    (List.Sublist.cons_cons _ (List.singleton_sublist.2 (exit_mem_of_collect hc))).trans
      (hpost.trans (localView_decode_sublist ρ k t))
  exact pair_of_sublist_filterMap h

theorem locOf_eq_out {ρ : Roles X I O C} {e : WEv} {b : O} (h : locOf ρ e = some (.out b)) :
    ∃ f a, e = .req f a ∧ ρ.callOut f a = some b := by
  cases e with
  | call f a => simp [locOf, tag, tagLoc] at h
  | ret f a r => rcases r with _ | r <;> simp [locOf, tag, tagLoc] at h
  | req f a =>
    simp only [locOf, tag] at h
    rcases ho : ρ.callOut f a with _ | o
    · rcases hi : ρ.callIn f a with _ | i <;> simp [ho, hi, tagLoc] at h
    · simp only [ho, Option.map_some, tagLoc, Tag.loc, Option.some.injEq, Loc.out.injEq] at h
      exact ⟨f, a, rfl, h ▸ ho⟩
  | imp f a r =>
    rcases r with _ | r
    · simp [locOf, tag] at h
    · simp only [locOf, tag] at h
      rcases hi : ρ.answerIn f a r with _ | i <;> simp [hi, tagLoc] at h

theorem locOf_eq_exit {ρ : Roles X I O C} {e : WEv} {c : C}
    (h : locOf ρ e = some (.exit (some c))) :
    ∃ f a res, e = .ret f a (some res) ∧ ρ.result f a res = some c := by
  cases e with
  | call f a => simp [locOf, tag, tagLoc] at h
  | ret f a r =>
    rcases r with _ | r
    · simp [locOf, tag, tagLoc] at h
    · simp only [locOf, tag, Option.map_some, tagLoc, Tag.loc, Option.some.injEq,
        Loc.exit.injEq] at h
      exact ⟨f, a, r, rfl, h⟩
  | req f a =>
    simp only [locOf, tag] at h
    rcases ho : ρ.callOut f a with _ | o
    · rcases hi : ρ.callIn f a with _ | i <;> simp [ho, hi, tagLoc] at h
    · simp [ho, tagLoc] at h
  | imp f a r =>
    rcases r with _ | r
    · simp [locOf, tag] at h
    · simp only [locOf, tag] at h
      rcases hi : ρ.answerIn f a r with _ | i <;> simp [hi, tagLoc] at h

/-! ## Runs of a component -/

theorem mem_ioRuns {Im Ex : Set FnName} (σ : Strategy (nsig Im) (nsig Ex)) (ρ : Roles X I O C)
    (r : Run I O C) : r ∈ ioRuns σ ρ ↔
      ∃ s ∈ σ, ∃ b ∈ wblocks (wtrace s), r ∈ windows (b.filterMap (locOf ρ)) := by
  constructor
  · rintro ⟨_, ⟨_, ⟨s, hs, rfl⟩, rfl⟩, hr⟩
    exact ⟨s, hs, (mem_inputRuns_decode (σ.legal hs) ρ r).1 hr⟩
  · rintro ⟨s, hs, h⟩
    exact ⟨_, ⟨_, ⟨s, hs, rfl⟩, rfl⟩, (mem_inputRuns_decode (σ.legal hs) ρ r).2 h⟩

theorem mem_entryIORuns {Im Ex : Set FnName} (σ : Strategy (nsig Im) (nsig Ex))
    (ρ : Roles X I O C) (r : Run X O C) : r ∈ entryIORuns σ ρ ↔
      ∃ s ∈ σ, ∃ b ∈ wblocks (wtrace s), entryRun (b.filterMap (locOf ρ)) = some r := by
  constructor
  · rintro ⟨_, ⟨_, ⟨s, hs, rfl⟩, rfl⟩, hr⟩
    exact ⟨s, hs, (mem_entryRuns_decode (σ.legal hs) ρ r).1 hr⟩
  · rintro ⟨s, hs, h⟩
    exact ⟨_, ⟨_, ⟨s, hs, rfl⟩, rfl⟩, (mem_entryRuns_decode (σ.legal hs) ρ r).2 h⟩

theorem triggers_ioRuns_sound {Im Ex : Set FnName} {σ : Strategy (nsig Im) (nsig Ex)}
    {ρ : Roles X I O C} {a : I} {b : O} (h : (a, b) ∈ triggers (ioRuns σ ρ)) :
    ∃ s ∈ σ, ∃ e₁ e₂, [e₁, e₂] <+ wtrace s ∧ locOf ρ e₁ = some (.inp a) ∧
      locOf ρ e₂ = some (.out b) := by
  obtain ⟨r, ⟨_, ⟨_, ⟨s, hs, rfl⟩, rfl⟩, hr⟩, rfl, hb⟩ := h
  exact ⟨s, hs, triggers_sound ρ hr hb⟩

theorem returns_ioRuns_sound {Im Ex : Set FnName} {σ : Strategy (nsig Im) (nsig Ex)}
    {ρ : Roles X I O C} {a : I} {c : C} (h : (a, c) ∈ returns (ioRuns σ ρ)) :
    ∃ s ∈ σ, ∃ e₁ e₂, [e₁, e₂] <+ wtrace s ∧ locOf ρ e₁ = some (.inp a) ∧
      locOf ρ e₂ = some (.exit (some c)) := by
  obtain ⟨bs, _, ⟨_, ⟨s, hs, rfl⟩, rfl⟩, hr⟩ := h
  exact ⟨s, hs, result_sound ρ hr rfl⟩

theorem entry_result_sound (ρ : Roles X I O C) {t : List WEv} {r : Run X O C}
    (hr : r ∈ entryRuns (decode (tag ρ) t)) {c : C} (hc : r.result = some c) :
    ∃ e₁ e₂, [e₁, e₂] <+ t ∧ locOf ρ e₁ = some (.enter (some r.input)) ∧
      locOf ρ e₂ = some (.exit (some c)) := by
  obtain ⟨k, hk⟩ := mem_entryRuns.1 hr
  have hsub := localView_decode_sublist ρ k t
  revert hk hsub
  generalize localView k (decode (tag ρ) t) = l
  intro hk hsub
  match l, hk with
  | .enter (some x) :: l', hk =>
    simp only [entryRun, Option.some.injEq] at hk
    subst hk
    have h : [Loc.enter (some x), .exit (some c)] <+ t.filterMap (locOf ρ) :=
      (List.Sublist.cons_cons _ (List.singleton_sublist.2 (exit_mem_of_collect hc))).trans hsub
    exact pair_of_sublist_filterMap h

theorem returns_entryIORuns_sound {Im Ex : Set FnName} {σ : Strategy (nsig Im) (nsig Ex)}
    {ρ : Roles X I O C} {x : X} {c : C} (h : (x, c) ∈ returns (entryIORuns σ ρ)) :
    ∃ s ∈ σ, ∃ e₁ e₂, [e₁, e₂] <+ wtrace s ∧ locOf ρ e₁ = some (.enter (some x)) ∧
      locOf ρ e₂ = some (.exit (some c)) := by
  obtain ⟨bs, _, ⟨_, ⟨s, hs, rfl⟩, rfl⟩, hr⟩ := h
  exact ⟨s, hs, entry_result_sound ρ hr rfl⟩

theorem mem_importAccepted_of_triggers {Im Ex : Set FnName} {σ : Strategy (nsig Im) (nsig Ex)}
    {inp out : FnName} {decI : List Val → Option I} {decO : List Val → Option O} {a : I} {b : O}
    (h : (a, b) ∈ triggers (ioRuns σ (importIO inp out decI decO))) :
    b ∈ Silmaril.Wasi.Accept.importAccepted σ out decO := by
  obtain ⟨s, hs, _, e₂, he, -, h₂⟩ := triggers_ioRuns_sound h
  obtain ⟨f, args, rfl, hf⟩ := locOf_eq_out h₂
  exact ⟨_, ⟨s, hs, rfl⟩, _, he.subset (List.mem_cons_of_mem _ List.mem_cons_self), hf⟩

end Silmaril.Proofs.Wasi.IOAccept
