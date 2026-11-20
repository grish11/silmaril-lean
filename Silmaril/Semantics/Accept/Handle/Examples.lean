module

public import Silmaril.Semantics.Accept.Handle.Thms

/-!
# Handle-based acceptance: examples and counterexamples

A toy writer `natW` builds natural numbers from literals (`lit n`) and successors (`succ`,
one child); handles are `ℕ`. Each example is a concrete trace; a trace set need not be prefix
closed, but where it matters the prefix-closed version is used.

* `callTrap_ne_ignore`: an invalid `accept` followed by a valid one **in the same export call**:
  accepted under `ignore`, not under the call-local trap (nor the session abort,
  `sessionTrap_ne_ignore`).
* `callTrap_ne_sessionTrap`: an invalid `accept` in one export call, a valid one in the next
  (`[accept 0, enter, write (lit 7) → 1, accept 1]`): accepted under the call-local trap, not
  under the session abort.
* `persist_seven`: store effects persist across a call-local trap: write `7` at `1`, an invalid
  accept (the call traps), a new export call, `accept 1` accepts `7`.
* `fixed_lt_ub`: on the prefix-closed module "write `succ [5]` (5 unallocated), accept the
  result", the UB top accepts `0`, while no fixed environment does: the result of an invalid
  write still has the constructor's shape. `fixed_trace_lt_ub`: on one trace, a later
  allocation pins down an earlier unallocated `accept`.
* `sentinel_twice`: a trace that receives the sentinel `0` twice accepts `10` with the sentinel
  and nothing without it (no sentinel-free environment answers `0` twice for different trees).
* `batch_not_downClosed`: batches are not downward closed, unlike the constructed set.
* `inter_strict`: languages of trace sets do not preserve intersections.
* `arbitrary_ne_ub`, `arbitrary_uncertified`: an always-invalid query. Arbitrary answers
  accept nothing on their own but break certified acceptance; UB accepts everything.
* `cycle_unfolds_to_nothing`: a self-referential node environment denotes no finite tree.
-/

@[expose] public section

namespace Silmaril.Accept.Handle.Examples

open Silmaril.Accept Silmaril.Accept.Host

/-- Literals and successors. -/
inductive NOp where
  | lit (n : ℕ)
  | succ

/-- The toy writer. -/
def natW : Writer NOp ℕ where
  build
    | .lit n, [] => some n
    | .succ, [m] => some (m + 1)
    | _, _ => none

theorem agrees_none' {r : ℕ} {t : ℕ} : Agrees (none : Option (Env ℕ ℕ)) r t := by
  intro ρ h; cases h

/-- The initial state, unfolded. -/
theorem init_eq : (WState.init : WState ℕ ℕ) = ⟨Env.empty, ∅, .live⟩ := rfl

/-! ## Call-local trap, session abort and ignore -/

def t1 : List (WEv NOp ℕ) := [.accept 0, .write (.lit 7) [] 1, .accept 1]

theorem seven_ignore : 7 ∈ writerLang natW {onAccept := .ignore} {t1} :=
  mem_lang.2 ⟨t1, rfl, _, _,
    .cons (.acceptIgnore rfl rfl) (.cons (.writeOk (t := 7) rfl ⟨by simp, .inl rfl⟩ agrees_none')
      (.cons (.acceptOk (t := 7) (by simp)) (.nil _))), by simp⟩

/-- Under the call-local trap the invalid accept aborts the call: the write in the same call
is not answered. -/
theorem callTrap_t1 : writerLang natW {onAccept := .callTrap} {t1} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨t, ht, s, A, hr, -⟩ := mem_lang.1 hx
  rw [Set.mem_singleton_iff] at ht
  subst ht
  change (writer natW _).Run ⟨Env.empty, ∅, .live⟩ t1 s A at hr
  cases hr with
  | cons hs hrest =>
      cases hs with
      | acceptOk h => cases h
      | acceptCallTrap _ _ => cases hrest with | cons hs' _ => cases hs'
      | acceptSessionTrap _ hp => cases hp
      | acceptIgnore _ hp => cases hp
      | acceptChaos _ hp _ => cases hp
      | acceptFixed _ _ hf => cases hf

theorem sessionTrap_t1 : writerLang natW {onAccept := .sessionTrap} {t1} = ∅ :=
  Set.subset_empty_iff.1 (callTrap_t1 ▸
    writerLang_sessionTrap_subset_callTrap (W := natW) {onAccept := .callTrap} {t1})

theorem callTrap_ne_ignore :
    writerLang natW {onAccept := .callTrap} {t1} ≠ writerLang natW {onAccept := .ignore} {t1} := by
  rw [callTrap_t1]; intro h; have := seven_ignore; rw [← h] at this; exact this

theorem sessionTrap_ne_ignore :
    writerLang natW {onAccept := .sessionTrap} {t1} ≠
      writerLang natW {onAccept := .ignore} {t1} := by
  rw [sessionTrap_t1]; intro h; have := seven_ignore; rw [← h] at this; exact this

/-- An invalid accept in the first export call, a valid one in the second. -/
def t5 : List (WEv NOp ℕ) := [.accept 0, .enter, .write (.lit 7) [] 1, .accept 1]

theorem seven_callTrap : 7 ∈ writerLang natW {onAccept := .callTrap} {t5} :=
  mem_lang.2 ⟨t5, rfl, _, _,
    .cons (.acceptCallTrap rfl rfl) (.cons .resume
      (.cons (.writeOk (t := 7) rfl ⟨by simp, .inl rfl⟩ agrees_none')
        (.cons (.acceptOk (t := 7) (by simp)) (.nil _)))), by simp⟩

theorem sessionTrap_t5 : writerLang natW {onAccept := .sessionTrap} {t5} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨t, ht, s, A, hr, -⟩ := mem_lang.1 hx
  rw [Set.mem_singleton_iff] at ht
  subst ht
  change (writer natW _).Run ⟨Env.empty, ∅, .live⟩ t5 s A at hr
  cases hr with
  | cons hs hrest =>
      cases hs with
      | acceptOk h => cases h
      | acceptCallTrap _ hp => cases hp
      | acceptSessionTrap _ _ => cases hrest with | cons hs' _ => cases hs'
      | acceptIgnore _ hp => cases hp
      | acceptChaos _ hp _ => cases hp
      | acceptFixed _ _ hf => cases hf

/-- **The call-local trap is strictly more permissive than the session abort**: a later export
call may still accept. -/
theorem callTrap_ne_sessionTrap :
    writerLang natW {onAccept := .callTrap} {t5} ≠
      writerLang natW {onAccept := .sessionTrap} {t5} := by
  rw [sessionTrap_t5]; intro h; have := seven_callTrap; rw [h] at this; exact this

/-- Write `7` at `1`, trap the call on an invalid accept, call again and accept `1`. -/
def t6 : List (WEv NOp ℕ) := [.write (.lit 7) [] 1, .accept 2, .enter, .accept 1]

/-- **Effects before a call-local trap persist**: the tree written before the trap is accepted
in the next export call. -/
theorem persist_seven : 7 ∈ writerLang natW {onAccept := .callTrap} {t6} :=
  mem_lang.2 ⟨t6, rfl, _, _,
    .cons (.writeOk (t := 7) rfl ⟨by simp, .inl rfl⟩ agrees_none')
      (.cons (.acceptCallTrap (by simp [Env.empty]) rfl) (.cons .resume
        (.cons (.acceptOk (t := 7) (by simp)) (.nil _)))), by simp⟩

/-! ## Fixed environments versus the UB top -/

/-- UB on invalid accepts and writes. -/
def polUB : Policy ℕ := {onAccept := .ub, onWrite := .ub}

/-- "Write `succ [5]`, accept the result", prefix closed. -/
def T2 : Set (List (WEv NOp ℕ)) := {[], [.write .succ [5] 1], [.write .succ [5] 1, .accept 1]}

theorem zero_ub : 0 ∈ writerLang natW polUB T2 := by
  refine mem_lang.2 ⟨[.write .succ [5] 1], by simp [T2], _, _,
    .cons (.writeChaos rfl rfl rfl) (.nil _), by simp⟩

theorem zero_not_fixed : 0 ∉ fixedLang natW polUB Set.univ T2 := by
  intro hx
  unfold fixedLang langOver at hx
  rw [Set.mem_iUnion] at hx
  obtain ⟨⟨ρ, _⟩, hx⟩ := hx
  obtain ⟨t, ht, s, A, hr, hxA⟩ := mem_lang.1 hx
  change (writer natW polUB (some ρ)).Run ⟨Env.empty, ∅, .live⟩ t s A at hr
  simp only [T2, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with rfl | rfl | rfl
  · cases hr; simp at hxA
  · cases hr with
    | cons hs hrest =>
        cases hrest
        cases hs with
        | writeOk hb _ _ => cases hb
        | writeFail hs _ => cases hs
        | writeChaos _ _ hf => cases hf
        | writeFixed _ _ _ _ _ _ => simp at hxA
  · cases hr with
    | cons hs hrest =>
        cases hs with
        | writeOk hb _ _ => cases hb
        | writeFail hs _ => cases hs
        | writeChaos _ _ hf => cases hf
        | @writeFixed σ B op args r t ρ' _ _ hfix hb _ _ =>
            cases hfix
            cases hrest with
            | cons hs' hnil =>
                cases hnil
                simp only [Set.union_empty, Set.empty_union] at hxA
                cases hs' with
                | acceptOk h =>
                    simp only [Function.update_self, Option.some.injEq] at h
                    subst h
                    simp only [Set.mem_singleton_iff] at hxA
                    subst hxA
                    simp only [Writer.built, Env.lookupAll, List.mapM_cons, List.mapM_nil,
                      Option.bind_eq_bind] at hb
                    rcases h5 : ρ 5 with _ | m <;> simp [h5, natW] at hb
                | acceptCallTrap h _ => simp at h
                | acceptSessionTrap h _ => simp at h
                | acceptIgnore h _ => simp at h
                | acceptChaos h _ _ => simp at h
                | acceptFixed h _ _ => simp at h

theorem fixed_lt_ub : fixedLang natW polUB Set.univ T2 ⊂ writerLang natW polUB T2 :=
  ⟨fixedLang_subset _ _ _, fun h => zero_not_fixed (h zero_ub)⟩

/-- One trace: accept the unallocated `5`, then allocate `5` for `7`. -/
def t2' : List (WEv NOp ℕ) := [.accept 5, .write (.lit 7) [] 5]

theorem fixed_trace : fixedLang natW polUB Set.univ {t2'} ⊆ {7} := by
  intro x hx
  unfold fixedLang langOver at hx
  rw [Set.mem_iUnion] at hx
  obtain ⟨⟨ρ, _⟩, hx⟩ := hx
  obtain ⟨t, rfl, s, A, hr, hxA⟩ := mem_lang.1 hx
  change (writer natW polUB (some ρ)).Run ⟨Env.empty, ∅, .live⟩ t2' s A at hr
  cases hr with
  | cons hs hrest =>
      cases hrest with
      | cons hs' hnil =>
          cases hnil
          cases hs with
          | acceptOk h => cases h
          | acceptCallTrap _ hp => cases hp
          | acceptSessionTrap _ hp => cases hp
          | acceptIgnore _ hp => cases hp
          | acceptChaos _ _ hf => cases hf
          | @acceptFixed σ B h ρ' _ _ hfix =>
              cases hfix
              cases hs' with
              | writeOk hb _ ha =>
                  simp [natW, Writer.built, Env.lookupAll] at hb
                  subst hb
                  have h5 := ha ρ rfl
                  rcases hxA with hxA | hxA | hxA
                  · simp only [Set.mem_ofPred_eq] at hxA
                    rw [h5] at hxA
                    exact Set.mem_singleton_iff.2 (Option.some.inj hxA).symm
                  · simp at hxA
                  · simp at hxA
              | writeFail hs _ => cases hs
              | writeChaos hb _ _ => cases hb
              | writeFixed hb _ _ _ _ _ => cases hb

theorem fixed_trace_lt_ub : 0 ∈ writerLang natW polUB {t2'} ∧
    0 ∉ fixedLang natW polUB Set.univ {t2'} :=
  ⟨mem_lang.2 ⟨t2', rfl, _, _, .cons (.acceptChaos rfl rfl rfl) (.cons (.chaos _) (.nil _)),
    by simp⟩, fun h => by simpa using fixed_trace h⟩

/-! ## A sentinel received twice -/

def polS : Policy ℕ := {sentinel := some 0}

/-- "Allocate `10`; if the next two allocations both return `0`, accept the first handle." -/
def t3 : List (WEv NOp ℕ) :=
  [.write (.lit 10) [] 1, .write (.lit 20) [] 0, .write (.lit 30) [] 0, .accept 1]

theorem ten_sentinel : 10 ∈ writerLang natW polS {t3} :=
  mem_lang.2 ⟨t3, rfl, _, _, .cons (.writeOk (t := 10) rfl ⟨by simp [polS], .inl rfl⟩ agrees_none')
    (.cons (.writeFail rfl (.inl rfl)) (.cons (.writeFail rfl (.inl rfl))
      (.cons (.acceptOk (t := 10) (by simp)) (.nil _)))), by simp⟩

theorem ten_not_without_sentinel : 10 ∉ writerLang natW {polS with sentinel := none} {t3} := by
  intro hx
  obtain ⟨t, rfl, s, A, hr, -⟩ := mem_lang.1 hx
  change (writer natW _).Run ⟨Env.empty, ∅, .live⟩ t3 s A at hr
  cases hr with
  | cons hs hrest =>
      cases hs with
      | writeFail hs _ => cases hs
      | writeChaos hb _ _ => cases hb
      | writeFixed _ _ hf => cases hf
      | writeOk _ _ _ =>
          cases hrest with
          | cons hs hrest =>
              cases hs with
              | writeFail hs _ => cases hs
              | writeChaos hb _ _ => cases hb
              | writeFixed _ _ hf => cases hf
              | writeOk hb2 _ _ =>
                  simp [natW, Writer.built, Env.lookupAll] at hb2
                  subst hb2
                  cases hrest with
                  | cons hs hrest =>
                      cases hs with
                      | writeFail hs _ => cases hs
                      | writeChaos hb _ _ => cases hb
                      | writeFixed _ _ hf => cases hf
                      | writeOk hb hf _ =>
                          simp [natW, Writer.built, Env.lookupAll] at hb
                          subst hb
                          rcases hf.2 with h | ⟨_, h⟩ <;> simp at h

theorem sentinel_twice :
    ¬ writerLang natW polS {t3} ⊆ writerLang natW {polS with sentinel := none} {t3} :=
  fun h => ten_not_without_sentinel (h ten_sentinel)

/-! ## Batches -/

/-- Unary trees: leaves and single-child nodes. -/
inductive Tr where
  | leaf (n : ℕ)
  | node (c : Tr)
  deriving DecidableEq

/-- The unary-tree writer. -/
def trW : Writer NOp Tr where
  build
    | .lit n, [] => some (.leaf n)
    | .succ, [m] => some (.node m)
    | _, _ => none

/-- The child relation of unary trees. -/
def Sub (c t : Tr) : Prop := t = .node c

theorem trW_childRel : trW.ChildRel Sub := by
  intro op ts t hb c hc
  cases op with
  | lit n =>
      match ts, hb with
      | [], hb => simp [trW] at hb; subst hb; simp [Sub] at hc
  | succ =>
      match ts, hb with
      | [m], hb => simp [trW] at hb; subst hb; simp [Sub] at hc; simp [hc]

/-- Build a leaf, drop the batch, build a node over it, keep the batch. -/
def t4 : List (WEv NOp ℕ) :=
  [.write (.lit 3) [] 1, .acceptBatch false, .write .succ [1] 2, .acceptBatch true]

theorem t4_lang : writerLang trW {} {t4} = {.node (.leaf 3)} := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨t, ht, s, A, hr, hxA⟩ := mem_lang.1 hx
    rw [Set.mem_singleton_iff] at ht
    subst ht
    change (writer trW _).Run ⟨Env.empty, ∅, .live⟩ t4 s A at hr
    cases hr with
    | cons hs hrest =>
        cases hs with
        | writeFail hs _ => cases hs
        | writeChaos hb _ _ => cases hb
        | writeFixed _ _ hf => cases hf
        | writeOk hb _ _ =>
            simp [trW, Writer.built, Env.lookupAll] at hb
            subst hb
            cases hrest with
            | cons hs hrest =>
                cases hs with
                | acceptBatch _ =>
                    cases hrest with
                    | cons hs hrest =>
                        cases hs with
                        | writeFail hs _ => cases hs
                        | writeChaos _ hu _ => cases hu
                        | writeFixed _ _ hf => cases hf
                        | writeOk hb _ _ =>
                            simp [trW, Writer.built, Env.lookupAll] at hb
                            subst hb
                            cases hrest with
                            | cons hs hrest =>
                                cases hs with
                                | acceptBatch _ =>
                                    cases hrest
                                    simpa using hxA
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact mem_lang.2 ⟨t4, rfl, _, _,
      .cons (.writeOk (t := .leaf 3) rfl ⟨by simp, .inl rfl⟩ (fun _ h => by cases h))
        (.cons (.acceptBatch false)
          (.cons (.writeOk (t := .node (.leaf 3)) (by simp [trW, Writer.built, Env.lookupAll])
              ⟨by simp, .inl (by simp [Env.empty])⟩ (fun _ h => by cases h))
            (.cons (.acceptBatch true) (.nil _)))), by simp⟩

theorem batch_not_downClosed : ¬ DownClosed Sub (writerLang trW {} {t4}) := by
  rw [t4_lang]
  intro h
  have := h (Set.mem_singleton _) (show Sub (.leaf 3) (.node (.leaf 3)) from rfl)
  simp at this

/-! ## Intersections -/

theorem inter_strict :
    1 ∈ writerLang natW {} {[.write (.lit 1) [] 1, .accept 1]} ∩
      writerLang natW {} {[.write (.lit 1) [] 2, .accept 2]} ∧
    writerLang natW {} ({[.write (.lit 1) [] 1, .accept 1]} ∩
      {[.write (.lit 1) [] 2, .accept 2]}) = ∅ := by
  have h1 : 1 ∈ writerLang natW {} {[.write (.lit 1) [] 1, .accept 1]} :=
    mem_lang.2 ⟨_, rfl, _, _, .cons (.writeOk (t := 1) rfl ⟨by simp, .inl rfl⟩ agrees_none')
      (.cons (.acceptOk (t := 1) (by simp)) (.nil _)), by simp⟩
  have h2 : 1 ∈ writerLang natW {} {[.write (.lit 1) [] 2, .accept 2]} :=
    mem_lang.2 ⟨_, rfl, _, _, .cons (.writeOk (t := 1) rfl ⟨by simp, .inl rfl⟩ agrees_none')
      (.cons (.acceptOk (t := 1) (by simp)) (.nil _)), by simp⟩
  refine ⟨⟨h1, h2⟩, ?_⟩
  have : ({[.write (.lit 1) [] 1, .accept 1]} ∩ {[.write (.lit 1) [] 2, .accept 2]} :
      Set (List (WEv NOp ℕ))) = ∅ := by
    ext t; simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
      iff_false, not_and]
    rintro rfl h; simp at h
  rw [this]; exact Host.lang_empty

/-! ## Readers: arbitrary answers versus UB -/

/-- A reader whose only query is never valid. -/
def R0 : Reader Unit Bool ℕ ℕ := ⟨fun _ _ => False, fun _ _ _ => False⟩

theorem arbitrary_ne_ub :
    readerLang R0 .arbitrary .callTrap Set.univ {[.read () true]} = ∅ ∧
    readerLang R0 .ub .callTrap Set.univ {[.read () true]} = Set.univ := by
  constructor
  · rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    unfold readerLang langOver at hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨⟨ρ, _⟩, hx⟩ := hx
    obtain ⟨t, ht, p, A, hr, hxA⟩ := mem_lang.1 hx
    rw [Set.mem_singleton_iff] at ht
    subst ht
    cases hr with
    | cons hs hnil =>
        cases hnil
        cases hs with
        | read _ _ => simp at hxA
        | readChaos hn => simp [answers, R0, badAnswers] at hn
  · rw [Set.eq_univ_iff_forall]
    intro x
    unfold readerLang langOver
    rw [Set.mem_iUnion]
    exact ⟨⟨Env.empty, Set.mem_univ _⟩, mem_lang.2 ⟨_, rfl, _, _,
      .cons (.readChaos (by simp [answers, R0, badAnswers])) (.nil _), by simp⟩⟩

/-- A certificate that is vacuously sound for the empty language. -/
def cert0 (hist : List (Unit × Bool)) (_ : ℕ) : Prop := hist ≠ []

theorem cert0_sound : CertSound R0 cert0 ∅ := by
  intro ρ hist h hf hc
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil hist hc
  exact absurd (hf p hp).1 id

theorem cert0_certified : Certified cert0 {[.read () true, .accept 0]} := by
  intro t ht u v h e
  rw [Set.mem_singleton_iff] at ht
  subst ht
  rcases u with _ | ⟨a, u⟩
  · simp at e
  · simp only [List.cons_append, List.cons.injEq] at e
    obtain ⟨rfl, -⟩ := e
    simp [cert0, REv.reads]

/-- **Arbitrary answers break certified acceptance**: the certified module accepts `5` in the
environment `0 ↦ 5` under `arbitrary`, although its certificate is sound for `∅` (and, by
`readerLang_trap_subset`, it accepts nothing under `trap`). -/
theorem arbitrary_uncertified :
    5 ∈ readerLang R0 .arbitrary .callTrap Set.univ {[.read () true, .accept 0]} ∧
    readerLang R0 .trap .callTrap Set.univ {[.read () true, .accept 0]} = ∅ := by
  constructor
  · unfold readerLang langOver
    rw [Set.mem_iUnion]
    exact ⟨⟨fun _ => some 5, Set.mem_univ _⟩, mem_lang.2 ⟨_, rfl, _, _,
      .cons (.read (by simp [answers, R0, badAnswers]) (Set.mem_univ true))
        (.cons (.acceptOk rfl) (.nil _)), by simp⟩⟩
  · exact Set.subset_empty_iff.1 (readerLang_trap_subset (by simp) cert0_sound cert0_certified _)

/-! ## Cycles -/

/-- Every node adds one to the sum of its children. -/
def mkSum (_ : Unit) (xs : List ℕ) : Option ℕ := some (xs.sum + 1)

/-- Handle `0` is its own child. -/
def loopEnv : NodeEnv ℕ Unit := fun _ => some ((), [0])

theorem cycle_unfolds_to_nothing (x : ℕ) : ¬ Unfold mkSum loopEnv 0 x :=
  not_unfold_of_cycle (size := id)
    (fun m xs x h c hc => by
      simp only [mkSum, Option.some.injEq] at h
      subst h
      have key : ∀ ys : List ℕ, c ∈ ys → c ≤ ys.sum := by
        intro ys
        induction ys with
        | nil => simp
        | cons y ys ih =>
            intro hm
            simp only [List.mem_cons] at hm
            rcases hm with rfl | hm
            · simp
            · have := ih hm; simp; omega
      have := key xs hc
      show c < xs.sum + 1
      omega)
    (.single ⟨(), [0], rfl, List.mem_singleton_self 0⟩) x

end Silmaril.Accept.Handle.Examples

namespace Silmaril.Accept.Handle.Examples

/-! ## One unused failure -/

/-- "Allocate `10`; allocate `20`, which fails; accept the first handle." -/
def t3one : List (WEv NOp ℕ) := [.write (.lit 10) [] 1, .write (.lit 20) [] 0, .accept 1]

/-- The single failure is unused afterwards, so `10` is also accepted without a sentinel (the
failure is read as allocating `20` at handle `0`). -/
theorem ten_one_failure : 10 ∈ writerLang natW {polS with sentinel := none} {t3one} :=
  writerLang_subset_of_oneFailure (W := natW) (pol := polS) rfl rfl
    (fun t ht => by
      rw [Set.mem_singleton_iff] at ht; subst ht
      refine .inr ⟨[.write (.lit 10) [] 1], .lit 20, [], [.accept 1], rfl, ?_, ?_, ?_⟩
      · intro op args h; simp at h
      · intro op args h; simp at h
      · intro e he; simp at he; subst he; simp [WEv.uses])
    (Host.mem_lang.2 ⟨t3one, rfl, _, _, .cons (.writeOk (t := 10) rfl ⟨by simp [polS], .inl rfl⟩
      agrees_none') (.cons (.writeFail rfl (.inl rfl)) (.cons (.acceptOk (t := 10) (by simp))
        (.nil _))), by simp⟩)

end Silmaril.Accept.Handle.Examples
