module

public import Silmaril.Games.Examples.Counter.Defs
public import Silmaril.Games.Institution.Thms

/-!
# The counter cell: worked examples

* `counter_exact`: `counter n ⊨ □ Exact n`, by an invariant of the transition system
  (`GSen.box_ofLTS`).
* `counter_mono`: `counter n ⊨ □ Mono`.
* The loose specification: `anyMono_sat` (`anyMono ⊨ □ Mono`), `counter_le_anyMono` and
  `sat_mono_iff_le`. The latter says that a strategy satisfies `□ Mono` iff it refines
  `anyMono`.
* The reduct along `ι` (expose `get` only):
  * `reduct_counter_const` proves `reduct ι (counter n) ⊨ □ ConstAns n` with the upper half
    `Strategy.restrict_sound`;
  * `counter_sat_translated` derives the translated sentence `senMap ι (□ ConstAns n)` for
    `counter n` through the satisfaction condition of `GInst`;
  * `counter_sat_pull` gives the same sentence in its play form `□ (pull ι (ConstAns n))`
    (`Game.map_box`).
-/

@[expose] public section

namespace Silmaril.Games.Examples.Counter

open Silmaril.Games GSen

/-! ## Moves and the count -/

@[simp] theorem getVal?_getA (k : ℕ) : getVal? (getA k) = some k := rfl
@[simp] theorem getVal?_incA : getVal? incA = none := rfl
@[simp] theorem getVal?_ask (q : CellOp) : getVal? (.inr (.ask q)) = none := rfl
@[simp] theorem bump_getA (k j : ℕ) : bump (getA k) j = j := rfl
@[simp] theorem bump_incA (j : ℕ) : bump incA j = j + 1 := rfl
@[simp] theorem bump_ask (q : CellOp) (j : ℕ) : bump (.inr (.ask q)) j = j := rfl

/-- Opponent moves are not answers. -/
theorem getVal?_of_isO {o : CMove} (h : o.IsO) : getVal? o = none ∧ ∀ k, bump o k = k := by
  rcases o with (⟨⟨⟩⟩ | ⟨⟨⟩, _⟩) | (⟨q⟩ | ⟨q, _⟩)
  · exact ⟨rfl, fun _ => rfl⟩
  · exact (h : False).elim

/-- A `get` answer does not change the count. -/
theorem bump_of_getVal? {o : CMove} {v : ℕ} (h : getVal? o = some v) (k : ℕ) : bump o k = k := by
  rcases o with (⟨⟨⟩⟩ | ⟨⟨⟩, _⟩) | (⟨q⟩ | ⟨q, _⟩)
  · rfl
  · cases q
    · rfl
    · cases h

/-- The count never decreases. -/
theorem le_bump (o : CMove) (k : ℕ) : k ≤ bump o k := by
  unfold bump
  split <;> omega

/-! ## Closure properties -/

/-- `exactFrom` is closed under prefixes. -/
theorem exactFrom_prefix {s t : List CMove} (h : s <+: t) {k : ℕ} (ht : exactFrom k t) :
    exactFrom k s := by
  induction t generalizing s k with
  | nil =>
    rw [List.prefix_nil.1 h]
    trivial
  | cons a t ih =>
    rcases List.prefix_cons_iff.1 h with rfl | ⟨s', rfl, hs'⟩
    · trivial
    · exact ⟨ht.1, ih hs' ht.2⟩

/-- `exactFrom` is closed under Opponent moves. -/
theorem exactFrom_append {s : List CMove} {o : CMove} (ho : o.IsO) {k : ℕ}
    (hs : exactFrom k s) : exactFrom k (s ++ [o]) := by
  induction s generalizing k with
  | nil =>
    refine ⟨fun v hv => ?_, trivial⟩
    rw [(getVal?_of_isO ho).1] at hv
    cases hv
  | cons a s ih => exact ⟨hs.1, ih hs.2⟩

/-- Runs of the cell from value `k` produce exact traces. -/
theorem exactFrom_run {x y : (lts 0).State} {s : List CMove} (h : (lts 0).Run x s y) :
    exactFrom x.2 s := by
  induction h with
  | nil => trivial
  | tau h => cases h
  | vis h _ ih =>
    cases h with
    | ask q k => exact ⟨fun v hv => (by cases hv), ih⟩
    | get k => exact ⟨fun v hv => (by cases hv; rfl), ih⟩
    | inc k => exact ⟨fun v hv => (by cases hv), ih⟩

/-- The traces of `lts n` are exactly those of `lts 0` from value `n`. -/
theorem run_lts {n : ℕ} {x y : (lts n).State} {s : List CMove} (h : (lts n).Run x s y) :
    (lts 0).Run x s y := by
  induction h with
  | nil => exact .nil _
  | tau h _ ih => exact .tau h ih
  | vis h _ ih => exact .vis h ih

/-! ## The counter satisfies its specifications -/

/-- **`counter n ⊨ □ Exact n`**. -/
theorem counter_exact (n : ℕ) : (box (Exact n)).holds (counter n) :=
  box_ofLTS (fun _ _ ht hst => exactFrom_prefix hst ht)
    (fun _ _ hs ho => exactFrom_append ho hs)
    (fun _ ⟨_, h⟩ => exactFrom_run (run_lts (n := n) h))

/-- Exact traces are monotone. -/
theorem monoFrom_of_exactFrom {s : List CMove} {j k : ℕ} (hs : exactFrom k s) (hjk : j ≤ k) :
    monoFrom j s := by
  induction s generalizing j k with
  | nil => trivial
  | cons o s ih =>
    refine ⟨fun v hv => hs.1 v hv ▸ hjk, ih hs.2 ?_⟩
    cases hv : getVal? o with
    | none => exact hjk.trans (le_bump o k)
    | some v =>
      rw [Option.getD_some, bump_of_getVal? hv, hs.1 v hv]

/-- **`counter n ⊨ □ Mono`**. -/
theorem counter_mono (n : ℕ) : (box Mono).holds (counter n) :=
  fun s hs => monoFrom_of_exactFrom (counter_exact n s hs) (Nat.zero_le n)

/-! ## The loose specification -/

/-- `anyMono ⊨ □ Mono`. -/
theorem anyMono_sat : (box Mono).holds anyMono := by
  intro s hs
  obtain ⟨σ, hσ, hs⟩ := (Strategy.mem_sSup_of_nonempty ⟨counter 0, counter_mono 0⟩).1 hs
  exact hσ s hs

/-- A strategy satisfies `□ Mono` iff it refines `anyMono`. -/
theorem sat_mono_iff_le (σ : Strategy Sig.empty cellSig) :
    (box Mono).holds σ ↔ σ ≤ anyMono :=
  ⟨fun h => le_sSup h, fun h => box_universal Mono h anyMono_sat⟩

/-- **Every counter refines the loose specification.** -/
theorem counter_le_anyMono (n : ℕ) : counter n ≤ anyMono :=
  (sat_mono_iff_le _).1 (counter_mono n)

/-! ## The reduct exposing `get` only -/

/-- Plays seen through `upGet` of exact plays answer the count. -/
theorem const_of_forall₂ {s : List CMove} {p : List (Move Sig.empty getOnly)}
    (h : List.Forall₂ (UpRel upGet) s p) {k : ℕ} (hs : exactFrom k s) :
    ∀ v : ℕ, (.inr (.ans (m := ()) v) : Move Sig.empty getOnly) ∈ p → v = k := by
  induction h generalizing k with
  | nil => intro v hv; cases hv
  | cons hab _ ih =>
    intro v hv
    cases hab with
    | low e => exact (match e with | .ask m => nomatch m | .ans m _ => nomatch m)
    | ask q =>
      rcases List.mem_cons.1 hv with hv | hv
      · cases hv
      · exact ih hs.2 v hv
    | ans q n =>
      rcases List.mem_cons.1 hv with hv | hv
      · cases hv
        exact hs.1 _ rfl
      · exact ih hs.2 v hv

/-- **The reduct of a counter along `ι` is a constant oracle.** -/
theorem reduct_counter_const (n : ℕ) : (box (ConstAns n)).holds (Game.reduct ι (counter n)) := by
  intro p hp
  rw [ι, Game.reduct_id_lo] at hp
  obtain ⟨s, hs, hr | ⟨p', q, rfl, hr⟩⟩ := Strategy.restrict_sound _ _ hp
  · exact const_of_forall₂ hr (counter_exact n s hs)
  · intro v hv
    rcases List.mem_append.1 hv with hv | hv
    · exact const_of_forall₂ hr (counter_exact n s hs) v hv
    · simp at hv

/-- **The translated sentence holds in the counter**, by the satisfaction condition of
`GInst`. -/
theorem counter_sat_translated (n : ℕ) :
    (Game.senMap ι (box (ConstAns n))).holds (counter n) :=
  (GInst.sat_iff ι (counter n) (box (ConstAns n))).2 (reduct_counter_const n)

/-- The same sentence in play form: `counter n ⊨ □ (pull ι (ConstAns n))`. -/
theorem counter_sat_pull (n : ℕ) : (box (Game.pull ι (ConstAns n))).holds (counter n) := by
  rw [← Game.map_box]
  exact counter_sat_translated n

/-- The reduct also satisfies the oracle form of monotonicity: any two answers are equal. -/
theorem reduct_counter_answers_eq (n : ℕ) {p : List (Move Sig.empty getOnly)}
    (hp : p ∈ Game.reduct ι (counter n)) {v w : ℕ}
    (hv : (.inr (.ans (m := ()) v) : Move Sig.empty getOnly) ∈ p)
    (hw : (.inr (.ans (m := ()) w) : Move Sig.empty getOnly) ∈ p) : v = w :=
  (reduct_counter_const n p hp v hv).trans (reduct_counter_const n p hp w hw).symm

end Silmaril.Games.Examples.Counter
