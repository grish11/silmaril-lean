module

public import Silmaril.Proofs.Games.Abstract.SessionLinkAssoc.Basic
public import Mathlib.Data.Nat.Find
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn

/-!
# Linking sessions: regrouping coherent services (proofs)

Coherent services `InfServe` of a server, cut into blocks and glued back:

* a prefix of a service is a list of rounds, and the rest is a service (`infServe_split`); a list
  of rounds followed by a service is a service (`infServe_prepend`);
* a stream of blocks of rounds, infinitely many of them nonempty, chained through stores, is a
  coherent service of the concatenated calls (`flat_serve`). The rounds of each block are annotated
  with their stores (`AChain`) and the annotated blocks are concatenated (`flatStream`);
* a finite list of rounds serving the concatenation of finitely many blocks of calls is cut into
  blocks of rounds (`rounds_blocks`).
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionLinkAssoc

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.SessionLink

universe u

/-! ## Streams -/

section Streams

variable {α : Type u}

theorem take_streamTake (ω : ℕ → α) {j k : ℕ} (h : j ≤ k) :
    (streamTake ω k).take j = streamTake ω j :=
  ((List.prefix_iff_eq_take.1 (streamTake_prefix ω h)).trans (by simp)).symm

/-- A prefix of a stream prefix is a stream prefix. -/
theorem streamTake_of_prefix {ω : ℕ → α} {L : List α} {M : ℕ} (h : L <+: streamTake ω M) :
    streamTake ω L.length = L := by
  rw [List.prefix_iff_eq_take.1 h, take_streamTake ω (by simpa using h.length_le)]
  simp only [length_streamTake]

theorem streamTake_congr {f g : ℕ → α} {n : ℕ} (h : ∀ k < n, f k = g k) :
    streamTake f n = streamTake g n := by
  simp only [streamTake]
  exact List.ofFn_inj.2 (funext fun i => h i i.2)

theorem streamTake_map {β : Type u} (f : α → β) (ω : ℕ → α) (n : ℕ) :
    streamTake (fun i => f (ω i)) n = (streamTake ω n).map f := by
  simp [streamTake, List.map_ofFn]; rfl

/-- A list followed by a stream. -/
def prependStream (L : List α) (ω : ℕ → α) : ℕ → α :=
  fun k => if h : k < L.length then L[k] else ω (k - L.length)

theorem streamTake_prependStream (L : List α) (ω : ℕ → α) (k : ℕ) :
    streamTake (prependStream L ω) (L.length + k) = L ++ streamTake ω k := by
  apply List.ext_getElem
  · simp
  · intro j h₁ h₂
    simp only [streamTake, List.getElem_ofFn, prependStream]
    rw [List.getElem_append]
    split_ifs with h
    · rfl
    · simp

@[simp] theorem prependStream_nil (ω : ℕ → α) : prependStream [] ω = ω := by
  funext k; simp [prependStream]

theorem prependStream_cons_zero (x : α) (L : List α) (ω : ℕ → α) :
    prependStream (x :: L) ω 0 = x := by
  simp [prependStream]

theorem prependStream_cons_succ (x : α) (L : List α) (ω : ℕ → α) (k : ℕ) :
    prependStream (x :: L) ω (k + 1) = prependStream L ω k := by
  simp only [prependStream, List.length_cons, Nat.add_lt_add_iff_right, List.getElem_cons_succ]
  split_ifs <;> first | rfl | (congr 1; omega)

theorem prependStream_append (L L' : List α) (ω : ℕ → α) :
    prependStream (L ++ L') ω = prependStream L (prependStream L' ω) := by
  induction L with
  | nil => simp
  | cons x L ih =>
    funext k
    cases k with
    | zero => simp [prependStream_cons_zero]
    | succ k => rw [List.cons_append, prependStream_cons_succ, prependStream_cons_succ, ih]

/-- A stream with a given prefix is that prefix followed by its rest. -/
theorem prefix_iff_prependStream {x y : ℕ → α} {P : List α} :
    (∀ k, streamTake x (P.length + k) = P ++ streamTake y k) ↔ x = prependStream P y := by
  constructor
  · intro h
    refine stream_ext fun k => ?_
    rw [← take_streamTake x (Nat.le_add_left k P.length), h,
      ← take_streamTake (prependStream P y) (Nat.le_add_left k P.length),
      streamTake_prependStream]
  · rintro rfl k
    exact streamTake_prependStream P y k

theorem prependStream_shift {x : ℕ → α} {P : List α} (h : streamTake x P.length = P) :
    x = prependStream P (fun k => x (P.length + k)) := by
  refine prefix_iff_prependStream.1 fun k => ?_
  rw [streamTake_add, h]

/-- The flattening of infinitely many lists, infinitely many of them nonempty. -/
noncomputable def flatStream (l : ℕ → List α)
    (hl : ∀ n, ∃ k, n < (streamTake l k).flatten.length) : ℕ → α :=
  fun j => ((streamTake l (Nat.find (hl j))).flatten)[j]'(Nat.find_spec (hl j))

theorem flatten_streamTake_mono (l : ℕ → List α) {i j : ℕ} (h : i ≤ j) :
    (streamTake l i).flatten <+: (streamTake l j).flatten := by
  obtain ⟨r, hr⟩ := streamTake_prefix l h
  exact ⟨r.flatten, by rw [← hr, List.flatten_append]⟩

theorem streamTake_flatStream (l : ℕ → List α)
    (hl : ∀ n, ∃ k, n < (streamTake l k).flatten.length) (k : ℕ) :
    streamTake (flatStream l hl) (streamTake l k).flatten.length = (streamTake l k).flatten := by
  apply List.ext_getElem
  · simp
  · intro j h₁ h₂
    have e : (streamTake (flatStream l hl) (streamTake l k).flatten.length)[j]'h₁ =
        flatStream l hl j := by simp [streamTake]
    rw [e]
    unfold flatStream
    rcases le_total (Nat.find (hl j)) k with h | h
    · exact (flatten_streamTake_mono l h).getElem _
    · exact ((flatten_streamTake_mono l h).getElem _).symm

/-- Lists that are not eventually empty have unbounded concatenations. -/
theorem eventually_nil_or_unbounded (l : ℕ → List α) :
    (∃ n, ∀ k, n ≤ k → l k = []) ∨ ∀ n, ∃ k, n ≤ (streamTake l k).flatten.length := by
  by_cases h : ∃ n, ∀ k, n ≤ k → l k = []
  · exact .inl h
  · refine .inr fun n => ?_
    push Not at h
    induction n with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ n ih =>
      obtain ⟨k, hk⟩ := ih
      obtain ⟨k', hk', hne⟩ := h k
      refine ⟨k' + 1, ?_⟩
      have h₁ := (flatten_streamTake_mono l hk').length_le
      rw [streamTake_succ, List.flatten_append, List.length_append]
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
      have := List.length_pos_iff.2 hne
      omega

end Streams

variable {E : Sig.{u}} {S A B : Type u}

theorem served_streamTake (g : ℕ → A × List (Call E) × (B ⊕ PUnit.{u + 1})) (j : ℕ) :
    served (streamTake g j) = streamTake (fun k => (⟨(g k).1, (g k).2.2⟩ : Call (sig1 A B))) j := by
  induction j with
  | zero => rfl
  | succ j ih => simp [streamTake_succ, served_append, ih]

theorem servedLog_streamTake (g : ℕ → A × List (Call E) × (B ⊕ PUnit.{u + 1})) (j : ℕ) :
    servedLog (streamTake g j) = logTake (fun k => (g k).2.1) j := by
  induction j with
  | zero => rfl
  | succ j ih => simp [streamTake_succ, servedLog_append, ih, logTake_succ]

/-! ## Services -/

section Serve

variable {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}

/-- The rounds of a service, as a stream. -/
def serveRounds (ω : ℕ → Call (sig1 A B)) (l : ℕ → List (Call E)) (N : ℕ) :
    ℕ → A × List (Call E) × (B ⊕ PUnit.{u + 1}) :=
  fun j => ((ω (N + j)).1, l (N + j), (ω (N + j)).2)

theorem served_serveRounds (ω : ℕ → Call (sig1 A B)) (l : ℕ → List (Call E)) (N n : ℕ) :
    served (streamTake (serveRounds ω l N) n) = streamTake (fun j => ω (N + j)) n := by
  rw [served_streamTake]; rfl

theorem servedLog_serveRounds (ω : ℕ → Call (sig1 A B)) (l : ℕ → List (Call E)) (N n : ℕ) :
    servedLog (streamTake (serveRounds ω l N) n) = logTake (fun j => l (N + j)) n := by
  rw [servedLog_streamTake]; rfl

theorem logTake_add (l : ℕ → List (Call E)) (N n : ℕ) :
    logTake l (N + n) = logTake l N ++ logTake (fun j => l (N + j)) n := by
  simp [logTake, streamTake_add]

/-- **A block of a service** is a list of rounds. -/
theorem rounds_block {s : S} {ω : ℕ → Call (sig1 A B)} {l : ℕ → List (Call E)} {st : ℕ → S}
    (h : InfServe t s ω l st) (N n : ℕ) :
    Rounds t (st N) (streamTake (serveRounds ω l N) n) (st (N + n)) := by
  induction n with
  | zero => exact .nil _
  | succ n ih =>
    rw [streamTake_succ]
    exact rounds_append ih (.cons (h.step (N + n)) (.nil _))

/-- **The rest of a service** is a service. -/
theorem infServe_shift {s : S} {ω : ℕ → Call (sig1 A B)} {l : ℕ → List (Call E)} {st : ℕ → S}
    (h : InfServe t s ω l st) (N : ℕ) :
    InfServe t (st N) (fun k => ω (N + k)) (fun k => l (N + k)) (fun k => st (N + k)) where
  zero := rfl
  step k := h.step (N + k)

/-- **Rounds followed by a service** are a service. -/
theorem infServe_prepend {s s' : S} {rt : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))}
    {ω : ℕ → Call (sig1 A B)} {l : ℕ → List (Call E)} {st : ℕ → S}
    (h : Rounds t s rt s') (hi : InfServe t s' ω l st) :
    ∃ st', InfServe t s (prependStream (served rt) ω) (prependStream (rt.map (·.2.1)) l) st' := by
  induction h with
  | nil => exact ⟨st, by simpa using hi⟩
  | @cons s s₁ s₂ a c b rs hr _ ih =>
    obtain ⟨st', h'⟩ := ih hi
    refine ⟨fun k => match k with | 0 => s | k + 1 => st' k, ⟨rfl, fun k => ?_⟩⟩
    cases k with
    | zero =>
      simp only [served_cons, List.map_cons, prependStream_cons_zero]
      rw [← h'.zero] at hr
      exact hr
    | succ k =>
      simp only [served_cons, List.map_cons, prependStream_cons_succ]
      exact h'.step k

theorem logTake_prependStream (L : List (List (Call E))) (l : ℕ → List (Call E)) (k : ℕ) :
    logTake (prependStream L l) (L.length + k) = L.flatten ++ logTake l k := by
  simp [logTake, streamTake_prependStream]

theorem flatten_map_log (rt : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) :
    (rt.map (·.2.1)).flatten = servedLog rt := by
  simp [servedLog, List.flatMap]

end Serve

/-! ## Annotated rounds -/

section Chain

variable {B' : Type u}

/-- Rounds annotated with their final stores, chained from a store. -/
def AChain (t : ObsTriple E S A B') : S → List (A × List (Call E) × B' × S) → Prop
  | _, [] => True
  | s, x :: L => (x.2.1, End.ret x.2.2.1 x.2.2.2) ∈ t.1 s x.1 ∧ AChain t x.2.2.2 L

/-- The store after annotated rounds. -/
def aend : S → List (A × List (Call E) × B' × S) → S
  | s, [] => s
  | _, x :: L => aend x.2.2.2 L

/-- Forget the final store of an annotated round. -/
def er (x : A × List (Call E) × B' × S) : A × List (Call E) × B' := (x.1, x.2.1, x.2.2.1)

variable {t : ObsTriple E S A B'}

theorem aend_append (s : S) (L₁ L₂ : List (A × List (Call E) × B' × S)) :
    aend s (L₁ ++ L₂) = aend (aend s L₁) L₂ := by
  induction L₁ generalizing s with
  | nil => rfl
  | cons x L ih => exact ih _

theorem achain_append {s : S} {L₁ L₂ : List (A × List (Call E) × B' × S)} :
    AChain t s (L₁ ++ L₂) ↔ AChain t s L₁ ∧ AChain t (aend s L₁) L₂ := by
  induction L₁ generalizing s with
  | nil => simp [AChain, aend]
  | cons x L ih =>
    simp only [List.cons_append, AChain, aend, ih]
    tauto

theorem achain_of_prefix {s : S} {L₁ L₂ : List (A × List (Call E) × B' × S)} (h : L₁ <+: L₂)
    (hc : AChain t s L₂) : AChain t s L₁ := by
  obtain ⟨r, rfl⟩ := h
  exact (achain_append.1 hc).1

theorem exists_achain {s s' : S} {rs : List (A × List (Call E) × B')} (h : Rounds t s rs s') :
    ∃ L, AChain t s L ∧ L.map er = rs ∧ aend s L = s' := by
  induction h with
  | nil s => exact ⟨[], trivial, rfl, rfl⟩
  | @cons s s₁ s₂ a c b rs hr _ ih =>
    obtain ⟨L, hL, h₁, h₂⟩ := ih
    exact ⟨(a, c, b, s₁) :: L, ⟨hr, hL⟩, by simp [h₁, er], h₂⟩

theorem rounds_of_achain {s : S} {L : List (A × List (Call E) × B' × S)} (h : AChain t s L) :
    Rounds t s (L.map er) (aend s L) := by
  induction L generalizing s with
  | nil => exact .nil _
  | cons x L ih => exact .cons h.1 (ih h.2)

end Chain

section Flat

variable {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}

/-- An annotated stream chained from `s` is a coherent service. -/
theorem infServe_of_chain {s : S} {G : ℕ → A × List (Call E) × (B ⊕ PUnit.{u + 1}) × S}
    (hG : ∀ M, AChain t s (streamTake G M)) :
    InfServe t s (fun i => ⟨(G i).1, (G i).2.2.1⟩) (fun i => (G i).2.1)
      (fun i => aend s (streamTake G i)) where
  zero := rfl
  step k := by
    have := hG (k + 1)
    rw [streamTake_succ, achain_append] at this
    simp only [streamTake_succ, aend_append]
    exact this.2.1

/-- **Flattening blocks of rounds into a coherent service.** -/
theorem flat_serve {rt : ℕ → List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))} {st : ℕ → S}
    (h : ∀ k, Rounds t (st k) (rt k) (st (k + 1)))
    (hu : ∀ n, ∃ k, n < (streamTake rt k).flatten.length) :
    ∃ ω l st', InfServe t (st 0) ω l st' ∧ ∀ k,
      streamTake ω (streamTake rt k).flatten.length = served (streamTake rt k).flatten ∧
      logTake l (streamTake rt k).flatten.length = servedLog (streamTake rt k).flatten := by
  choose P hP₁ hP₂ hP₃ using fun k => exists_achain (h k)
  have hF : ∀ k, AChain t (st 0) (streamTake P k).flatten ∧
      aend (st 0) (streamTake P k).flatten = st k := by
    intro k
    induction k with
    | zero => exact ⟨trivial, rfl⟩
    | succ k ih =>
      rw [streamTake_succ, List.flatten_append, achain_append, aend_append]
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil, ih.2]
      exact ⟨⟨ih.1, hP₁ k⟩, hP₃ k⟩
  have hmap : ∀ k, (streamTake P k).flatten.map er = (streamTake rt k).flatten := by
    intro k
    rw [List.map_flatten, ← streamTake_map]
    simp only [hP₂]
  have hlen : ∀ k, (streamTake P k).flatten.length = (streamTake rt k).flatten.length := by
    intro k; rw [← hmap, List.length_map]
  have hl : ∀ n, ∃ k, n < (streamTake P k).flatten.length := fun n => by
    obtain ⟨k, hk⟩ := hu n
    exact ⟨k, by rw [hlen]; exact hk⟩
  set G := flatStream P hl
  have hGk : ∀ k, streamTake G (streamTake rt k).flatten.length = (streamTake P k).flatten := by
    intro k; rw [← hlen]; exact streamTake_flatStream P hl k
  have hG : ∀ M, AChain t (st 0) (streamTake G M) := by
    intro M
    obtain ⟨k, hk⟩ := hl M
    refine achain_of_prefix (streamTake_prefix G hk.le) ?_
    rw [hlen, hGk]
    exact (hF k).1
  refine ⟨_, _, _, infServe_of_chain hG, fun k => ⟨?_, ?_⟩⟩
  · rw [streamTake_map (fun x => (⟨x.1, x.2.2.1⟩ : Call (sig1 A B))) G, hGk, ← hmap]
    simp [served, er, Function.comp_def]
  · simp only [logTake]
    rw [streamTake_map (fun x => x.2.1) G, hGk, ← hmap, servedLog]
    simp [er, List.flatMap, Function.comp_def]

end Flat

/-! ## Cutting finitely many blocks -/

section Blocks

variable {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}

/-- **Rounds serving finitely many blocks of calls** cut into blocks of rounds. -/
theorem rounds_blocks {s : S} {lu : ℕ → List (Call (sig1 A B))} :
    ∀ (n : ℕ) {RT : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))} {s' : S},
      Rounds t s RT s' → served RT = logTake lu n →
      ∃ (rt : ℕ → List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) (st : ℕ → S),
        st 0 = s ∧ st n = s' ∧ (∀ k < n, Rounds t (st k) (rt k) (st (k + 1)) ∧
          served (rt k) = lu k) ∧ servedLog RT = logTake (fun k => servedLog (rt k)) n
  | 0, RT, s', h, hs => by
    obtain rfl := served_eq_nil.1 hs
    obtain rfl := rounds_nil_iff.1 h
    exact ⟨fun _ => [], fun _ => s, rfl, rfl, fun k hk => absurd hk (Nat.not_lt_zero _), rfl⟩
  | n + 1, RT, s', h, hs => by
    rw [logTake_succ] at hs
    obtain ⟨RT₁, RT₂, rfl, h₁, h₂⟩ := served_eq_append hs
    obtain ⟨sm, hr₁, hr₂⟩ := rounds_of_append h
    obtain ⟨rt, st, hst₀, hstn, hk, hlog⟩ := rounds_blocks n hr₁ h₁
    refine ⟨fun k => if k = n then RT₂ else rt k, fun k => if k = n + 1 then s' else st k,
      by simp [hst₀], by simp, fun k hk' => ?_, ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hk' | rfl
      · simp only [Nat.ne_of_lt hk', show k ≠ n + 1 by omega, show k + 1 ≠ n + 1 by omega,
          ↓reduceIte]
        exact hk k hk'
      · simp only [show k ≠ k + 1 by omega, ↓reduceIte]
        exact ⟨hstn ▸ hr₂, h₂⟩
    · have e : logTake (fun k => servedLog (if k = n then RT₂ else rt k)) n =
          logTake (fun k => servedLog (rt k)) n := by
        unfold logTake
        rw [streamTake_congr (g := fun k => servedLog (rt k))
          fun k hk' => by simp [Nat.ne_of_lt hk']]
      rw [logTake_succ, servedLog_append, hlog, e]
      simp

/-- **Rounds serving finitely many blocks of calls** cut into a stream of blocks of rounds, empty
after the last block. -/
theorem rounds_blocks' {s s' : S} {lu : ℕ → List (Call (sig1 A B))} {n : ℕ}
    {RT : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))} (hlu : ∀ k, n ≤ k → lu k = [])
    (h : Rounds t s RT s') (hs : served RT = logTake lu n) :
    ∃ (rt : ℕ → List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) (st : ℕ → S),
      st 0 = s ∧ (∀ k, Rounds t (st k) (rt k) (st (k + 1)) ∧ served (rt k) = lu k) ∧
        (∀ k, n ≤ k → rt k = []) ∧ servedLog RT = logTake (fun k => servedLog (rt k)) n := by
  obtain ⟨rt, st, hst₀, hstn, hk, hlog⟩ := rounds_blocks n h hs
  refine ⟨fun k => if k < n then rt k else [], fun k => if k ≤ n then st k else s',
    by simp [hst₀], fun k => ?_, fun k hk' => by simp [show ¬k < n by omega], ?_⟩
  · by_cases hkn : k < n
    · simp only [hkn, show k ≤ n by omega, show k + 1 ≤ n by omega, ↓reduceIte]
      exact hk k hkn
    · simp only [hkn, ↓reduceIte, served_nil, hlu k (by omega), and_true]
      by_cases hkn' : k = n
      · subst hkn'
        simp only [le_refl, ↓reduceIte, show ¬k + 1 ≤ k by omega, hstn]
        exact .nil _
      · simp only [show ¬k ≤ n by omega, show ¬k + 1 ≤ n by omega, ↓reduceIte]
        exact .nil _
  · rw [hlog]
    unfold logTake
    rw [streamTake_congr (g := fun k => servedLog (if k < n then rt k else []))
      fun k hk' => by simp [hk']]

theorem served_flatten (rt : ℕ → List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) (k : ℕ) :
    served (streamTake rt k).flatten = logTake (fun k => served (rt k)) k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [streamTake_succ, logTake_succ, ih]

theorem servedLog_flatten (rt : ℕ → List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) (k : ℕ) :
    servedLog (streamTake rt k).flatten = logTake (fun k => servedLog (rt k)) k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [streamTake_succ, logTake_succ, ih]

theorem rounds_flatten {rt : ℕ → List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))} {st : ℕ → S}
    (h : ∀ k, Rounds t (st k) (rt k) (st (k + 1))) (m : ℕ) :
    Rounds t (st 0) (streamTake rt m).flatten (st m) := by
  induction m with
  | zero => exact .nil _
  | succ m ih =>
    rw [streamTake_succ, List.flatten_append]
    simpa using rounds_append ih (h m)

end Blocks

/-! ## More streams -/

section More

variable {α : Type u}

theorem prependStream_add (L : List α) (ω : ℕ → α) (k : ℕ) :
    prependStream L ω (L.length + k) = ω k := by
  simp [prependStream]

theorem prependStream_of_le {L : List α} (ω : ℕ → α) {k : ℕ} (h : L.length ≤ k) :
    prependStream L ω k = ω (k - L.length) := by
  simp [prependStream, show ¬k < L.length by omega]

/-- Logs that do not grow over a range are empty on it. -/
theorem logTake_nil_of_eq {l : ℕ → List (Call E)} {a m : ℕ}
    (h : logTake l (a + m) = logTake l a) {j : ℕ} (hj : j < m) : l (a + j) = [] := by
  rw [logTake_add] at h
  have h' : logTake (fun j => l (a + j)) m = [] := by
    simpa using h
  exact List.flatten_eq_nil_iff.1 h' _ (List.mem_ofFn.2 ⟨⟨j, hj⟩, rfl⟩)

theorem length_logTake_mono (l : ℕ → List (Call E)) {j k : ℕ} (h : j ≤ k) :
    (logTake l j).length ≤ (logTake l k).length :=
  (logTake_mono l h).length_le

end More

end Silmaril.Proofs.Games.Abstract.SessionLinkAssoc
