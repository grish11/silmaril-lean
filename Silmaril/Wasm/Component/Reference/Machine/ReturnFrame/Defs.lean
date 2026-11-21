module

public import Silmaril.Wasm.Component.Reference.Machine.Step.Defs

@[expose] public section

namespace Silmaril.Wasm.Component.Machine.ReturnFrame

open Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime

abbrev Continuation (E : CoreEngine) (Host : Type) := Ret E → P E Host (Ret E)

variable {E : CoreEngine} {Host : Type}

abbrev Substitutions (E : CoreEngine) (Host : Type) := Continuation E Host → Continuation E Host → Prop

/-- The relation used for a single saved call. -/
inductive Only (first second : Continuation E Host) : Substitutions E Host where
  | here : Only first second first second

/-- Installing another call does not discard previously paired frames. -/
inductive Extend (older : Substitutions E Host) (first second : Continuation E Host) : Substitutions E Host where
  | existing {left right} : older left right → Extend older first second left right
  | current : Extend older first second first second

namespace Related

variable (changes : Substitutions E Host)

/-- Unchanged frames (including newly pushed frames) pair by reflexivity.
Only the given substitutions may change a saved program continuation. -/
inductive Segment : Seg E Host → Seg E Host → Prop where
  | same (frame) : Segment frame frame
  | swap {first second} : changes first second → Segment (.prog first) (.prog second)

inductive Active : Activation E Host → Activation E Host → Prop where
  | mk {thread focus left right} (frames : List.Forall₂ (Segment changes) left right) :
      Active ⟨thread, focus, left⟩ ⟨thread, focus, right⟩

inductive Saved : Option (Activation E Host) → Option (Activation E Host) → Prop where
  | none : Saved none none
  | some {left right} : Active changes left right → Saved (some left) (some right)

/-- The paired machines share all reached data. Only suspended program
frames can differ, including frames of blocked activations. -/
inductive Paired : Config E Host → Config E Host → Prop where
  | mk {left : Config E Host} {active saved}
      (control : List.Forall₂ (Active changes) left.ctl active)
      (blocked : List.Forall₂ (Saved changes) left.conts saved) :
      Paired left { left with ctl := active, conts := saved }

/-- Both machines reached the saved return frame. The pop changes only
the program focus and segment stack, not the store or host state. -/
inductive Returned : Config E Host → Config E Host → Label E Host → Config E Host → Config E Host → Prop where
  | mk {left right : Config E Host} {first second thread value leftFrames rightFrames leftRest rightRest}
      (edge : changes first second)
      (leftAt : left.ctl = ⟨thread, .prog (.pure value), .prog first :: leftFrames⟩ :: leftRest)
      (rightAt : right.ctl = ⟨thread, .prog (.pure value), .prog second :: rightFrames⟩ :: rightRest) :
      Returned left right .tau
        { left with ctl := ⟨thread, .prog (first value), leftFrames⟩ :: leftRest }
        { right with ctl := ⟨thread, .prog (second value), rightFrames⟩ :: rightRest }

end Related

abbrev Segment (first second : Continuation E Host) := Related.Segment (Only first second)
abbrev Active (first second : Continuation E Host) := Related.Active (Only first second)
abbrev Saved (first second : Continuation E Host) := Related.Saved (Only first second)
abbrev Paired (first second : Continuation E Host) := Related.Paired (Only first second)
abbrev Returned (first second : Continuation E Host) := Related.Returned (Only first second)

end Silmaril.Wasm.Component.Machine.ReturnFrame
