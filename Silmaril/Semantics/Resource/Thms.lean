module

public import Silmaril.Semantics.Resource.Defs
import Silmaril.Proofs.Semantics.Resource.Laws

public section

namespace Silmaril.Semantics.Resource

universe s i o k v i' o'

variable {State : Type s} {Input : Type i} {Output : Type o} {Key : Type k}
  {Observation : Type v} {NextInput : Type i'} {NextOutput : Type o'}
  {first : Contract State Input Output Key} {second : Contract State NextInput NextOutput Key}
  {observe : State → Key → Observation} {next : Input → Output → NextInput}

/-- Sequencing preserves the common observation outside either operation's writes. -/
theorem Contract.seq_frames (hfirst : first.Frames observe) (hsecond : second.Frames observe) :
    (first.seq second next).Frames observe :=
  Silmaril.Proofs.Semantics.Resource.seq_frames hfirst hsecond

/-- A framed assertion has the same truth value across the transition when
none of its read keys may be written. -/
theorem Contract.Frames.assertion_iff (frame : first.Frames observe)
    {input : Input} {before after : State} {output : Output}
    (step : first.step input before output after)
    {reads : List Key} {assertion : State → Prop} (stable : DependsOn observe reads assertion)
    (disjoint : ∀ key ∈ reads, key ∉ first.writes input output) :
    assertion before ↔ assertion after :=
  stable fun key member => frame step key (disjoint key member)

end Silmaril.Semantics.Resource
