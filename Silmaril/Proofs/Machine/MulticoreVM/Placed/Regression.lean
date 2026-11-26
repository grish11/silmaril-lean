module

public import Silmaril.Machine.MulticoreVM.Institution.Placed.Thms
public import Silmaril.Machine.MulticoreVM.Placed.Outcomes.Thms
public import Silmaril.Machine.MulticoreVM.Toy.Thms
public import Silmaril.Semantics.ConcurrentTrace.Thms

namespace Silmaril.Machine.MulticoreVM.Placed

open CategoryTheory
open Institution (Sig placedToNamed namedToConcurrent)
open Silmaril.Semantics.ConcurrentTrace (Word ofWord ofWord_eq_iff swap swap_eq_iff)

private abbrev Rig (n : Nat) := Config (Fin n) Toy.ThreadId Unit Toy.Core

private abbrev threadStore {n : Nat} : StoreView (Fin n) Toy.ThreadId Unit Toy.Core Toy.Config :=
  fun _ threads => threads

private def instruction {n : Nat} :
    Instruction (Fin n) Toy.ThreadId Unit Toy.Core (Option Toy.ThreadId) Nat :=
  ofThreadStep Toy.step

private def oneCore (threads : Toy.Config) (running : Option Toy.ThreadId)
    (present : ∀ ⦃t⦄, running = some t → (threads t).isSome) : Rig 1 where
  cores := fun _ => some ()
  threads := threads
  placement := fun _ => running
  endpoints := fun {_ _} h => ⟨rfl, present h⟩
  unique := fun {_ _ _} _ _ => Subsingleton.elim _ _

private def bootThreads : Toy.Config := Toy.init 0 ⟨1, [.spawn 7 [.add 2, .emit], .emit]⟩
private def spawnedThreads : Toy.Config :=
  Toy.put (Toy.put bootThreads 0 ⟨1, [.emit]⟩) 1 ⟨7, [.add 2, .emit]⟩
private def addedThreads : Toy.Config := Toy.put spawnedThreads 1 ⟨9, [.emit]⟩
private def finishedThreads : Toy.Config := Toy.put addedThreads 1 ⟨9, []⟩

private def oneBoot : Rig 1 := oneCore bootThreads (some 0) (by rintro _ ⟨⟩; rfl)
private def oneSpawned : Rig 1 := oneCore spawnedThreads (some 0) (by rintro _ ⟨⟩; rfl)
private def oneAssigned : Rig 1 := oneCore spawnedThreads (some 1) (by rintro _ ⟨⟩; rfl)
private def oneAdded : Rig 1 := oneCore addedThreads (some 1) (by rintro _ ⟨⟩; rfl)
private def oneEmitted : Rig 1 := oneCore finishedThreads (some 1) (by rintro _ ⟨⟩; rfl)
private def oneIdle : Rig 1 := oneCore finishedThreads none (by intro _ h; cases h)

-- Spawn allocates the child while the parent still occupies the only core.
example : (oneSpawned.threads 1).isSome ∧ (∀ c, oneSpawned.placement c ≠ some 1) :=
  ⟨rfl, fun _ h => by cases h⟩

example {word final} : ¬ Step instruction (.execute 0 1 none) oneSpawned word final := by
  intro h
  cases h with
  | execute resident _ => cases resident

private def oneSchedule : Schedule (Fin 1) Toy.ThreadId (Option Toy.ThreadId) :=
  [.execute 0 0 (some 1), .assign 0 1, .execute 0 1 none, .execute 0 1 none, .idle 0]

private def oneWord : TaggedWord (Fin 1) Toy.ThreadId Nat := [.sync 0 0 [0, 1], .event 0 1 9]

private theorem oneRun : Scheduled instruction oneSchedule oneBoot oneWord oneIdle := by
  refine .cons (next := oneSpawned) (fragment := [.sync 0 0 [0, 1]])
    (.execute (fragment := [.sync [0, 1]]) rfl ⟨rfl, rfl, rfl⟩) ?_
  refine .cons (next := oneAssigned)
    (.assign (core := 0) (thread := 1) (initial := oneSpawned) rfl rfl (fun _ h => by cases h)
      ⟨rfl, rfl, ?_⟩) ?_
  · funext c
    rw [show c = 0 from Subsingleton.elim _ _, Function.update_self]
    rfl
  refine .cons (next := oneAdded) (.execute (fragment := []) rfl ⟨rfl, rfl, rfl⟩) ?_
  refine .cons (next := oneEmitted) (.execute (fragment := [.event 9]) rfl ⟨rfl, rfl, rfl⟩) ?_
  refine .cons (next := oneIdle)
    (.idle (core := 0) (initial := oneEmitted) rfl ⟨rfl, rfl, ?_⟩) (.nil oneIdle)
  funext c
  rw [show c = 0 from Subsingleton.elim _ _, Function.update_self]
  rfl

-- Three instructions survive, including the silent add. Both placement commands disappear.
example : (oneIdle.threads, [.sync [0, 1], .event 1 9]) ∈
    namedOutcomes (run Toy.step 3) oneBoot.threads :=
  oneRun.mem_threadRun (ofThreadStep_refines Toy.step)

example : coreWord oneWord = [.event 0 none, .event 0 (some 9)] ∧ oneIdle.placement 0 = none :=
  ⟨rfl, rfl⟩

example : (oneIdle.threads, ofWord ([.sync [0, 1], .event 1 9] : Word Toy.ThreadId Nat)) ∈
    observeQuotient '' namedOutcomes (run Toy.step 3) oneBoot.threads :=
  observeThreadQuotient_image_subset_run (view := threadStore) (ofThreadStep_refines Toy.step)
    oneSchedule oneBoot
    (Set.mem_image_of_mem (observeThreadQuotient threadStore) (show (oneIdle, oneWord) ∈
      taggedOutcomes instruction oneSchedule oneBoot from oneRun))

-- The abstract scheduler can select the waiting child. The concrete schedule cannot.
example : let child := (addedThreads, ofWord ([] : Word Toy.ThreadId Nat))
    child ∈ observeQuotient '' namedOutcomes (run Toy.step 1) oneSpawned.threads ∧
    child ∉ observeThreadQuotient threadStore '' taggedOutcomes instruction [.execute 0 1 none] oneSpawned := by
  have add : MulticoreVM.Scheduled Toy.step [⟨1, none⟩] oneSpawned.threads [] addedThreads :=
    .cons (fragment := []) rfl (.nil addedThreads)
  refine ⟨Set.mem_image_of_mem observeQuotient
    ((mem_run_iff_exists_schedule 1).mpr ⟨_, rfl, add⟩), ?_⟩
  rintro ⟨⟨final, word⟩, concrete, _⟩
  change Scheduled instruction [.execute 0 1 none] oneSpawned word final at concrete
  cases concrete with
  | cons first _ => cases first with
    | execute resident _ => cases resident

private abbrev oneSig : Sig := ⟨Toy.ThreadId, Fin 1, Nat⟩
private abbrev renamedSig : Sig := ⟨Option Nat, Bool, Bool⟩

private noncomputable def renameOne : oneSig ⟶ renamedSig where
  core := fun _ => true
  thread := ⟨some, fun _ _ => Option.some.inj⟩
  event := fun value => value == 9

-- Typed renaming takes the original participant list through the institution and quotient.
example : (placedToNamed ≫ namedToConcurrent).app renamedSig (Sig.Hom.mapPlaced renameOne oneWord) =
    ofWord ([.sync [some 0, some 1], .event (some 1) true] : renamedSig.NamedWord) := rfl

private def pairThreads : Toy.Config := Toy.put (Toy.init 0 ⟨4, [.emit]⟩) 1 ⟨9, [.emit]⟩

private def twoCores (threads : Toy.Config) (left right : Option Toy.ThreadId)
    (atLeft : ∀ ⦃t⦄, left = some t → (threads t).isSome)
    (atRight : ∀ ⦃t⦄, right = some t → (threads t).isSome)
    (distinct : ∀ t, left = some t → right ≠ some t) : Rig 2 where
  cores := fun _ => some ()
  threads := threads
  placement := fun c => if c = 0 then left else right
  endpoints := by
    intro c t h
    refine ⟨rfl, ?_⟩
    by_cases hc : c = 0
    · exact atLeft (by simpa [hc] using h)
    · exact atRight (by simpa [hc] using h)
  unique := by
    intro c d t hc hd
    have other (i : Fin 2) (hi : i ≠ 0) : i = 1 := by omega
    by_cases leftC : c = 0 <;> by_cases leftD : d = 0
    · exact leftC.trans leftD.symm
    · exact (distinct t (by simpa [leftC] using hc) (by simpa [leftD] using hd)).elim
    · exact (distinct t (by simpa [leftD] using hd) (by simpa [leftC] using hc)).elim
    · exact (other c leftC).trans (other d leftD).symm

private def twoBoot : Rig 2 :=
  twoCores pairThreads (some 0) none (by rintro _ ⟨⟩; rfl) (by intro _ h; cases h)
    (by intro _ _ h; cases h)
private def twoMoved : Rig 2 :=
  twoCores pairThreads none (some 0) (by intro _ h; cases h) (by rintro _ ⟨⟩; rfl)
    (by intro _ h; cases h)
private def twoAssigned : Rig 2 :=
  twoCores pairThreads (some 1) (some 0) (by rintro _ ⟨⟩; rfl) (by rintro _ ⟨⟩; rfl)
    (by rintro _ ⟨⟩ h; cases h)
private def twoFinal : Rig 2 :=
  twoCores (Toy.put pairThreads 0 ⟨4, []⟩) (some 1) (some 0)
    (by rintro _ ⟨⟩; rfl) (by rintro _ ⟨⟩; rfl) (by rintro _ ⟨⟩ h; cases h)

-- Assignment cannot duplicate a resident thread, even onto an idle core.
example {word final} : ¬ Step instruction (.assign 1 0) twoBoot word final := by
  intro h
  cases h with
  | assign _ _ waiting _ => exact waiting 0 rfl

private theorem twoRun : Scheduled instruction
    [.migrate 0 1, .assign 0 1, .execute 1 0 none] twoBoot [.event 1 0 4] twoFinal := by
  refine .cons (next := twoMoved)
    (.migrate (source := 0) (target := 1) (initial := twoBoot) rfl rfl rfl ⟨rfl, rfl, ?_⟩) ?_
  · funext c
    have hc : c = 0 ∨ c = 1 := by omega
    rcases hc with rfl | rfl <;> rfl
  refine .cons (next := twoAssigned)
    (.assign (core := 0) (thread := 1) (initial := twoMoved) rfl rfl ?_ ⟨rfl, rfl, ?_⟩) ?_
  · intro c
    have hc : c = 0 ∨ c = 1 := by omega
    rcases hc with rfl | rfl <;> decide
  · funext c
    have hc : c = 0 ∨ c = 1 := by omega
    rcases hc with rfl | rfl <;> rfl
  exact .cons (.execute (fragment := [.event 4]) rfl ⟨rfl, rfl, rfl⟩) (.nil twoFinal)

example : MulticoreVM.Scheduled Toy.step [⟨0, none⟩] twoBoot.threads [.event 0 4] twoFinal.threads :=
  twoRun.refines (ofThreadStep_refines Toy.step)

example : twoFinal.placement 0 = some 1 ∧ twoFinal.placement 1 = some 0 ∧
    Nat.card twoFinal.Resident ≤ 2 :=
  ⟨rfl, rfl, by simpa using twoFinal.resident_card_le⟩

-- Two different threads time-share one core. Their differently valued events commute in the
-- thread quotient, whereas the two images on the same core are dependent.
private def parentOnOnlyCore : TaggedLetter (Fin 1) Toy.ThreadId Nat := .event 0 0 4
private def childOnOnlyCore : TaggedLetter (Fin 1) Toy.ThreadId Nat := .event 0 1 9

example : let a := parentOnOnlyCore; let b := childOnOnlyCore
    ofWord (threadWord [a, b]) = ofWord (threadWord [b, a]) ∧
    ofWord (coreWord [a, b]) ≠ ofWord (coreWord [b, a]) := by
  refine ⟨swap (.events (by decide)), ?_⟩
  intro same
  rcases (swap_eq_iff parentOnOnlyCore.dropThread childOnOnlyCore.dropThread).mp same with
    equal | independent
  · cases equal
  · cases independent with
    | events different => exact different rfl

-- A migrating thread can emit on two different cores. Those core events commute, while the
-- corresponding events of the same thread are dependent.
private def beforeMigration : TaggedLetter (Fin 2) Toy.ThreadId Nat := .event 0 0 4
private def afterMigration : TaggedLetter (Fin 2) Toy.ThreadId Nat := .event 1 0 9

example : let a := beforeMigration; let b := afterMigration
    ofWord (coreWord [a, b]) = ofWord (coreWord [b, a]) ∧
    ofWord (threadWord [a, b]) ≠ ofWord (threadWord [b, a]) := by
  refine ⟨swap (.events (by decide)), ?_⟩
  intro same
  rcases (swap_eq_iff beforeMigration.dropCore afterMigration.dropCore).mp same with
    equal | independent
  · cases equal
  · cases independent with
    | events different => exact different rfl

end Silmaril.Machine.MulticoreVM.Placed
