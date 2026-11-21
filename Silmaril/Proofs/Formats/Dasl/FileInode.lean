module

public import Silmaril.Formats.Dasl.FileInode.Defs

public section

namespace Silmaril.Proofs.Formats.Dasl.FileInode

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.FileInode

variable {Name : Type} {limits : Limits} {observed extension : Snapshot Name}

private theorem sumLengths {rel : Child Name → Bytes → Prop} {inode chunks}
    (matching : List.Forall₂ rel inode chunks)
    (lengths : ∀ child data, rel child data → data.length = child.size) (index : Nat) :
    (chunks.take index).flatten.length = size (inode.take index) := by
  induction matching generalizing index with
  | nil => simp [size]
  | cons hit _ ih =>
    cases index with
    | zero => rfl
    | succ index => simpa [List.flatten_cons, size, lengths _ _ hit] using ih index

theorem resolvesLength {depth link length data}
    (valid : Resolves limits extension depth link length data) : data.length = length := by
  induction depth generalizing link length data with
  | zero => exact valid.elim
  | succ depth ih =>
    cases link with
    | blob name =>
      obtain ⟨page, _, lengthEq, _, rfl⟩ := valid
      exact Array.length_toList.trans lengthEq
    | obj name =>
      obtain ⟨inode, chunks, _, _, lengthEq, matching, rfl⟩ := valid
      have cover := sumLengths matching (fun _ _ => ih) (inode.length + chunks.length)
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at cover
      exact cover.trans lengthEq

theorem prefixLength {depth : Nat} {inode : Inode Name} {chunks : List Bytes}
    (matching : List.Forall₂ (fun child => Resolves limits extension depth child.link child.size) inode chunks)
    (index : Nat) : (chunks.take index).flatten.length = size (inode.take index) :=
  sumLengths matching (fun _ _ => resolvesLength) index

private theorem sliceAppend (head tail : Bytes) (length offset count : Nat)
    (lengthEq : head.length = length) :
    slice (head ++ tail) offset count =
      slice head offset (min count (length - offset)) ++
      slice tail (offset - length) (count - min count (length - offset)) := by
  subst length
  simp only [slice, List.drop_append, List.take_append, List.length_drop]
  by_cases enough : count ≤ head.length - offset
  · rw [Nat.min_eq_left enough, show count - (head.length - offset) = count - count by omega]
  · have full : (head.drop offset).length ≤ count := by rw [List.length_drop]; omega
    rw [Nat.min_eq_right (by omega), List.take_of_length_le full,
      ← List.length_drop, List.take_length]

private structure Matches {Payload : Type} (complete : Prop)
    (actual expected : Except (Error Name) Payload) : Prop where
  sound : ∀ data, actual = .ok data → expected = .ok data
  exactWhen : complete → actual = expected

private theorem same {Payload : Type} {complete : Prop} (result : Except (Error Name) Payload) :
    Matches complete result result := ⟨fun _ hit => hit, fun _ => rfl⟩

private theorem Matches.bind {Input Output : Type} {complete : Prop}
    {actual : Except (Error Name) Input} {item : Input} (matchFirst : Matches complete actual (.ok item))
    {actualNext : Input → Except (Error Name) Output} {expected : Except (Error Name) Output}
    (matchNext : Matches complete (actualNext item) expected) :
    Matches complete (actual >>= actualNext) expected := by
  constructor
  · intro data hit
    cases actual with
    | error error => cases hit
    | ok fetched =>
      have initial := matchFirst.sound fetched rfl
      cases initial
      exact matchNext.sound data hit
  · intro complete
    rw [matchFirst.exactWhen complete]
    exact matchNext.exactWhen complete

private theorem fetchMatches {Payload : Type} {complete : Prop} {link : Link Name}
    {result : Wire.ReadResult Payload} {expected : Payload}
    (sound : result = .found expected ∨ ∀ data, result ≠ .found data)
    (exactWhen : complete → result = .found expected) :
    Matches complete (fetch link result) (.ok expected) := by
  refine ⟨?_, fun done => by rw [exactWhen done]; rfl⟩
  intro data hit
  rcases sound with found | notFound
  · rw [found] at hit
    exact hit
  · cases result with
    | missing => cases hit
    | invalidWire => cases hit
    | found item => exact (notFound item rfl).elim

private theorem scanMatches {rel : Child Name → Bytes → Prop} {complete : Prop}
    {visitChild : Child Name → Nat → Nat → Except (Error Name) Bytes} {inode chunks}
    (matching : List.Forall₂ rel inode chunks)
    (lengths : ∀ child data, rel child data → data.length = child.size)
    (correct : ∀ child data, rel child data → ∀ offset count,
      Matches complete (visitChild child offset count) (.ok (slice data offset count)))
    (offset count : Nat) :
    Matches complete (scan visitChild inode offset count) (.ok (slice chunks.flatten offset count)) := by
  induction matching generalizing offset count with
  | nil => simpa [scan, slice] using same (.ok [])
  | @cons child data rest chunks hit _ ih =>
    let here := min count (child.size - offset)
    have head : Matches complete (if here = 0 then .ok [] else visitChild child offset here)
        (.ok (slice data offset here)) := by
      split
      · rename_i empty
        simpa [slice, empty] using same (.ok [])
      · exact correct child data hit offset here
    have tail := ih (offset - child.size) (count - here)
    rw [List.flatten_cons, sliceAppend data chunks.flatten child.size offset count (lengths _ _ hit)]
    rw [scan]
    apply head.bind
    apply tail.bind
    exact same _

private theorem agreedFetch {Payload : Type} {link : Link Name}
    {readObserved readExtension : Wire.ReadResult Payload} {expected : Payload} {complete : Prop}
    (agrees : ∀ item, readObserved = .found item → readExtension = .found item)
    (hit : readExtension = .found expected) (completeAgrees : complete → readObserved = readExtension) :
    Matches complete (fetch link readObserved) (.ok expected) := by
  apply fetchMatches _ (fun done => (completeAgrees done).trans hit)
  cases observedResult : readObserved with
  | missing => exact Or.inr (by intro _ contradiction; cases contradiction)
  | invalidWire => exact Or.inr (by intro _ contradiction; cases contradiction)
  | found item =>
    have equal := (agrees item observedResult).symm.trans hit
    cases equal
    exact Or.inl rfl

private theorem visitMatches (agrees : observed.Agrees extension) (fuel : Nat)
    {depth : Nat} {child : Child Name} {data : Bytes}
    (valid : Resolves limits extension depth child.link child.size data) (offset count : Nat) :
    Matches (observed = extension ∧ depth ≤ fuel)
      (visit limits observed fuel child offset count) (.ok (slice data offset count)) := by
  induction fuel generalizing depth child data offset count with
  | zero =>
    refine ⟨(fun _ hit => by cases hit), ?_⟩
    rintro ⟨_, depthBound⟩
    obtain rfl : depth = 0 := by omega
    exact valid.elim
  | succ fuel ih =>
    cases depth with
    | zero => exact valid.elim
    | succ depth =>
      cases linkEq : child.link with
      | blob name =>
        rw [linkEq] at valid
        obtain ⟨page, hit, lengthEq, pageBound, rfl⟩ := valid
        have pageMatch := agreedFetch (link := child.link) (complete := observed = extension ∧ depth + 1 ≤ fuel + 1)
          (readObserved := observed.blobs name) (readExtension := extension.blobs name)
          (fun _ hit => agrees.blobs hit) hit (fun done => by rw [done.1])
        simp only [linkEq] at pageMatch
        simp only [visit, linkEq]
        apply pageMatch.bind
        have bound := lengthEq ▸ pageBound
        simp only [lengthEq, bound, and_self, ite_true]
        exact same _
      | obj name =>
        rw [linkEq] at valid
        obtain ⟨inode, chunks, hit, fit, lengthEq, matching, rfl⟩ := valid
        have inodeMatch := agreedFetch (link := child.link) (complete := observed = extension ∧ depth + 1 ≤ fuel + 1)
          (readObserved := observed.objects name) (readExtension := extension.objects name)
          (fun _ hit => agrees.objects hit) hit (fun done => by rw [done.1])
        simp only [linkEq] at inodeMatch
        simp only [visit, linkEq]
        apply inodeMatch.bind
        simp only [fit, lengthEq, decide_true, Bool.and_self, ite_true]
        exact scanMatches matching (fun _ _ => resolvesLength) (fun _ _ valid offset count =>
          ⟨(ih valid offset count).sound, fun done => (ih valid offset count).exactWhen ⟨done.1, by omega⟩⟩)
          offset count

private def rangeResult (range : Option (Nat × Nat)) (length : Nat) (data : Bytes) : Except (Error Name) Bytes :=
  let (offset, count) := range.getD (0, length)
  if offset + count ≤ length then .ok (slice data offset count) else .error (.outOfBounds length)

private theorem readMatches (agrees : observed.Agrees extension) (fuel : Nat)
    {depth : Nat} {root : Name} {length : Nat} {data : Bytes}
    (valid : Resolves limits extension depth (.obj root) length data) (range : Option (Nat × Nat)) :
    Matches (observed = extension ∧ depth ≤ fuel) (read limits observed fuel root range)
      (rangeResult range length data) := by
  cases fuel with
  | zero =>
    refine ⟨(fun _ hit => by cases hit), ?_⟩
    rintro ⟨_, depthBound⟩
    obtain rfl : depth = 0 := by omega
    exact valid.elim
  | succ fuel =>
    cases depth with
    | zero => exact valid.elim
    | succ depth =>
      obtain ⟨inode, chunks, hit, fit, lengthEq, matching, rfl⟩ := valid
      have inodeMatch := agreedFetch (link := .obj root) (complete := observed = extension ∧ depth + 1 ≤ fuel + 1)
        (readObserved := observed.objects root) (readExtension := extension.objects root)
        (fun _ hit => agrees.objects hit) hit (fun done => by rw [done.1])
      unfold FileInode.read
      apply inodeMatch.bind
      simp only [fit, rangeResult, lengthEq]
      generalize range.getD (0, length) = window
      obtain ⟨offset, count⟩ := window
      by_cases bound : offset + count ≤ length
      · simp only [bound, ite_true]
        exact scanMatches matching (fun _ _ => resolvesLength) (fun _ _ valid offset count =>
          ⟨(visitMatches agrees fuel valid offset count).sound, fun done =>
            (visitMatches agrees fuel valid offset count).exactWhen ⟨done.1, by omega⟩⟩) offset count
      · simpa [bound] using same (.error (.outOfBounds length))

private theorem reflexive (store : Snapshot Name) : store.Agrees store := ⟨fun {_ _} hit => hit, fun {_ _} hit => hit⟩

theorem rangeSound (agrees : observed.Agrees extension) {fuel depth root length data offset count result}
    (valid : Resolves limits extension depth (.obj root) length data)
    (hit : read limits observed fuel root (some (offset, count)) = .ok result) :
    offset + count ≤ length ∧ result = slice data offset count := by
  have reference := (readMatches agrees fuel valid (some (offset, count))).sound result hit
  by_cases bound : offset + count ≤ length
  · exact ⟨bound, by simpa [rangeResult, bound, eq_comm] using reference⟩
  · simp [rangeResult, bound] at reference

theorem rangeComplete {fuel depth root length data offset count}
    (valid : Resolves limits extension depth (.obj root) length data) (enough : depth ≤ fuel) :
    read limits extension fuel root (some (offset, count)) =
      if offset + count ≤ length then .ok (slice data offset count) else .error (.outOfBounds length) :=
  (readMatches (reflexive extension) fuel valid _).exactWhen ⟨rfl, enough⟩

theorem recoverSound (agrees : observed.Agrees extension) {fuel depth root length data result}
    (valid : Resolves limits extension depth (.obj root) length data)
    (hit : read limits observed fuel root none = .ok result) : result = data := by
  have reference := (readMatches agrees fuel valid none).sound result hit
  have whole : slice data 0 length = data := by rw [← resolvesLength valid]; simp [slice]
  simpa [rangeResult, whole, eq_comm] using reference

theorem recoverComplete {fuel depth root length data}
    (valid : Resolves limits extension depth (.obj root) length data) (enough : depth ≤ fuel) :
    read limits extension fuel root none = .ok data := by
  have complete := (readMatches (reflexive extension) fuel valid none).exactWhen ⟨rfl, enough⟩
  have whole : slice data 0 length = data := by rw [← resolvesLength valid]; simp [slice]
  simpa [rangeResult, whole] using complete

end Silmaril.Proofs.Formats.Dasl.FileInode
