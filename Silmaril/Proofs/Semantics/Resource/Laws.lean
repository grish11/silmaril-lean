module

public import Silmaril.Semantics.Resource.Defs

public section

namespace Silmaril.Proofs.Semantics.Resource

open Silmaril.Semantics.Resource

universe s i o k v i' o'

variable {State : Type s} {Input : Type i} {Output : Type o} {Key : Type k}
  {Observation : Type v} {NextInput : Type i'} {NextOutput : Type o'}
  {first : Contract State Input Output Key} {second : Contract State NextInput NextOutput Key}
  {observe : State → Key → Observation} {next : Input → Output → NextInput}

theorem seq_frames (hfirst : first.Frames observe) (hsecond : second.Frames observe) :
    (first.seq second next).Frames observe := by
  intro input before reply after step key untouched
  obtain ⟨middle, stepFirst, stepSecond⟩ := step
  simp only [Contract.seq, List.mem_append, not_or] at untouched
  exact (hsecond stepSecond key untouched.2).trans (hfirst stepFirst key untouched.1)

end Silmaril.Proofs.Semantics.Resource
