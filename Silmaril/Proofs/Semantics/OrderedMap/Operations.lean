module

public import Silmaril.Semantics.OrderedMap.Operations.Defs

public section

namespace Silmaril.Proofs.Semantics.OrderedMap.Operations

open Silmaril.Semantics Silmaril.Semantics.OrderedMap

variable {Key Payload Error : Type} [LinearOrder Key]

theorem mem_domain (map : OrderedMap Key Payload) (key : Key) :
    key ∈ map.domain ↔ (map.lookup? key).isSome := by
  simp only [domain, keys, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨⟨_, value⟩, hit, rfl⟩
    simp [map.lookup_eq_some_iff.mpr hit]
  · intro present
    obtain ⟨value, found⟩ := Option.isSome_iff_exists.mp present
    exact ⟨(key, value), map.lookup_eq_some_iff.mp found, rfl⟩

theorem cardinality_eq (map : OrderedMap Key Payload) : map.cardinality = map.domain.card := by
  rw [domain, List.toFinset_card_of_nodup map.keys_nodup]
  simp [cardinality, keys]

theorem submap_spec [DecidableEq Payload] (left right : OrderedMap Key Payload) :
    left.submap right = true ↔ ∀ key value, left.lookup? key = some value → right.lookup? key = some value := by
  rw [submap, List.all_eq_true]
  exact ⟨fun holds key value present => of_decide_eq_true (holds _ (left.lookup_eq_some_iff.mp present)),
    fun holds entry present => decide_eq_true (holds entry.1 entry.2 (left.lookup_eq_some_iff.mpr present))⟩

private theorem evaluate_sound (step : Key → Except Error (Option Payload))
    {keys : List Key} {ordered : keys.Pairwise (· < ·)} {found : Evaluation (Payload := Payload) keys}
    (checked : evaluate step keys ordered = .ok found) :
    ∀ key ∈ keys, step key = .ok (found.map.lookup? key) := by
  induction keys with
  | nil => simp
  | cons first rest ih =>
    cases firstHit : step first with
    | error error => simp [evaluate, firstHit, Bind.bind, Except.bind] at checked
    | ok value =>
      cases tailHit : evaluate step rest ordered.of_cons with
      | error error => simp [evaluate, firstHit, tailHit, Bind.bind, Except.bind] at checked
      | ok tail =>
        have sound := ih tailHit
        have firstAbsent : tail.map.lookup? first = none := by
          cases hit : tail.map.lookup? first with
          | none => rfl
          | some payload =>
            have mem := tail.keys_mem _ (tail.map.lookup_eq_some_iff.mp hit)
            exact (lt_irrefl _ ((List.pairwise_cons.mp ordered).1 _ mem)).elim
        intro key hit
        rcases List.mem_cons.mp hit with rfl | mem
        · cases value <;>
            simp [evaluate, firstHit, tailHit, Bind.bind, Except.bind, Pure.pure, Except.pure] at checked <;>
            subst found
          · rw [firstHit, firstAbsent]
          · simp [firstHit, lookup?]
        · have different : first ≠ key := ne_of_lt ((List.pairwise_cons.mp ordered).1 _ mem)
          have tailResult := sound key mem
          cases value <;>
            simp [evaluate, firstHit, tailHit, Bind.bind, Except.bind, Pure.pure, Except.pure] at checked <;>
            subst found
          · exact tailResult
          · simpa only [lookup?, List.lookup_cons, beq_false_of_ne different.symm] using tailResult

private theorem evaluate_complete (step : Key → Except Error (Option Payload))
    {keys : List Key} (ordered : keys.Pairwise (· < ·))
    (ok : ∀ key ∈ keys, ∃ value, step key = .ok value) : ∃ result, evaluate step keys ordered = .ok result := by
  induction keys with
  | nil => exact ⟨_, rfl⟩
  | cons first rest ih =>
    obtain ⟨value, firstHit⟩ := ok first (by simp)
    obtain ⟨tail, tailHit⟩ := ih ordered.of_cons (fun key hit => ok key (List.mem_cons_of_mem _ hit))
    cases value <;> simp [evaluate, firstHit, tailHit, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem combine_spec (kind : Combine) (overlap : Overlap Key Payload Error) (left right result : OrderedMap Key Payload) :
    left.combine kind overlap right = .ok result ↔
      ∀ key, kind.atKey overlap key (left.lookup? key) (right.lookup? key) = .ok (result.lookup? key) := by
  let step := fun key => kind.atKey overlap key (left.lookup? key) (right.lookup? key)
  let keys := left.domain ∪ right.domain
  let ordered := ((keys.pairwise_sort (· ≤ ·)).and (keys.sort_nodup (· ≤ ·))).imp
    (fun pair => lt_of_le_of_ne pair.1 pair.2)
  change (evaluate step (keys.sort (· ≤ ·)) ordered).map Evaluation.map = .ok result ↔ _
  have sound {found} (checked : evaluate step (keys.sort (· ≤ ·)) ordered = .ok found) (key : Key) :
      step key = .ok (found.map.lookup? key) := by
    by_cases mem : key ∈ keys
    · exact evaluate_sound step checked key ((Finset.mem_sort _).mpr mem)
    · have neither : key ∉ left.domain ∧ key ∉ right.domain := by simpa [keys] using mem
      have empty (map : OrderedMap Key Payload) (absent : key ∉ map.domain) : map.lookup? key = none := by
        cases lookup : map.lookup? key with
        | none => rfl
        | some value => exact (absent ((mem_domain map key).mpr (by simp [lookup]))).elim
      have missing : found.map.lookup? key = none := by
        cases lookup : found.map.lookup? key with
        | none => rfl
        | some value => exact (mem ((Finset.mem_sort _).mp
            (found.keys_mem _ (found.map.lookup_eq_some_iff.mp lookup)))).elim
      cases kind <;> simp [step, Combine.atKey, empty left neither.1, empty right neither.2, missing]
  constructor
  · intro checked
    cases run : evaluate step (keys.sort (· ≤ ·)) ordered with
    | error error => simp [run, Except.map] at checked
    | ok found =>
      have equal : found.map = result := by simpa [run, Except.map] using checked
      simpa [step, equal] using sound run
  · intro pointwise
    obtain ⟨found, run⟩ := evaluate_complete step ordered (fun key _ => ⟨_, pointwise key⟩)
    have equal : found.map = result := eq_of_lookup fun key =>
      Except.ok.inj ((sound run key).symm.trans (pointwise key))
    simp [run, Except.map, equal]

theorem combine_succeeds_iff (kind : Combine) (overlap : Overlap Key Payload Error) (left right : OrderedMap Key Payload) :
    (∃ result, left.combine kind overlap right = .ok result) ↔
      ∀ key leftValue rightValue, left.lookup? key = some leftValue → right.lookup? key = some rightValue →
        ∃ value, overlap key leftValue rightValue = .ok value := by
  constructor
  · rintro ⟨result, ok⟩ key leftValue rightValue leftHit rightHit
    exact ⟨_, by simpa [leftHit, rightHit, Combine.atKey] using (combine_spec kind overlap left right result).mp ok key⟩
  · intro available
    have all (key : Key) : ∃ value, kind.atKey overlap key (left.lookup? key) (right.lookup? key) = .ok value := by
      cases leftHit : left.lookup? key <;> cases rightHit : right.lookup? key
      · cases kind <;> exact ⟨_, rfl⟩
      · cases kind <;> exact ⟨_, rfl⟩
      · cases kind <;> exact ⟨_, rfl⟩
      · exact available key _ _ leftHit rightHit
    unfold Silmaril.Semantics.OrderedMap.combine
    dsimp only
    obtain ⟨result, ok⟩ := evaluate_complete _ (keys := (left.domain ∪ right.domain).sort (· ≤ ·))
      (((left.domain ∪ right.domain).pairwise_sort (· ≤ ·)).and ((left.domain ∪ right.domain).sort_nodup (· ≤ ·)) |>.imp
        fun ordered => lt_of_le_of_ne ordered.1 ordered.2) (fun key _ => all key)
    exact ⟨result.map, by simp [ok, Except.map]⟩

theorem combine_reject_succeeds_iff (kind : Combine) (left right : OrderedMap Key Payload) :
    (∃ result, left.combine kind Overlap.reject right = .ok result) ↔ Disjoint left.domain right.domain := by
  rw [combine_succeeds_iff, Finset.disjoint_left]
  simp only [Overlap.reject, reduceCtorEq, exists_false]
  constructor
  · intro avoid key leftMem rightMem
    obtain ⟨leftValue, leftHit⟩ := Option.isSome_iff_exists.mp ((mem_domain left key).mp leftMem)
    obtain ⟨rightValue, rightHit⟩ := Option.isSome_iff_exists.mp ((mem_domain right key).mp rightMem)
    exact avoid key leftValue rightValue leftHit rightHit
  · intro avoid key _ _ leftHit rightHit
    exact avoid ((mem_domain left key).mpr (by simp [leftHit])) ((mem_domain right key).mpr (by simp [rightHit]))

theorem combine_membership (kind : Combine) (overlap : Overlap Key Unit Error)
    (left right result : OrderedSet Key) (ok : left.combine kind overlap right = .ok result) (key : Key) :
    kind.atKey overlap key (if left.contains key then some () else none) (if right.contains key then some () else none) =
      .ok (if result.contains key then some () else none) := by
  have view (set : OrderedSet Key) : (if set.contains key then some () else none) = set.lookup? key := by
    unfold Silmaril.Semantics.OrderedSet.contains
    cases set.lookup? key <;> simp
  simpa only [view] using (combine_spec kind overlap left right result).mp ok key

end Silmaril.Proofs.Semantics.OrderedMap.Operations
