module

public import Silmaril.Machine.MulticoreVM.Institution.Defs
public import Silmaril.Machine.MulticoreVM.Placed.Defs

/-! # Chronological observations of the VM with core placement -/

@[expose] public section

namespace Silmaril.Machine.MulticoreVM.Institution

open CategoryTheory
open Silmaril.Semantics.ConcurrentTrace (Word mapWord)

universe u

/-- The complete core-and-thread word from the placed VM, including the actor on a sync. -/
abbrev Sig.PlacedWord (A : Sig.{u}) := Placed.TaggedWord A.CoreId A.ThreadId A.Event

/-- The core-local word of the placed VM. A sync is an opaque `none` event. -/
abbrev Sig.CoreLocalWord (A : Sig.{u}) := Word A.CoreId (Option A.Event)

variable {A B : Sig.{u}}

/-- Rename every field of a placed observation, including the actor and participants of a sync. -/
def Sig.Hom.mapPlaced (f : A ⟶ B) (word : A.PlacedWord) : B.PlacedWord :=
  word.map fun
    | .event core thread value => .event (f.core core) (f.thread thread) (f.event value)
    | .sync core thread participants => .sync (f.core core) (f.thread thread) (participants.map f.thread)

/-- Rename a core-local word, retaining the distinction between a payload and a sync marker. -/
def Sig.Hom.mapCoreLocal (f : A ⟶ B) (word : A.CoreLocalWord) : B.CoreLocalWord :=
  mapWord f.core (Option.map f.event) word

/-- The placed VM's behavior consists of the words of all successful finite schedules. -/
def ofPlaced {Core Thread Choice : Type u} [DecidableEq A.CoreId]
    (instruction : Placed.Instruction A.CoreId A.ThreadId Core Thread Choice A.Event)
    (initial : Placed.Config A.CoreId A.ThreadId Core Thread) : Model A.PlacedWord :=
  { word | ∃ schedule final, Placed.Scheduled instruction schedule initial word final }

end Silmaril.Machine.MulticoreVM.Institution
