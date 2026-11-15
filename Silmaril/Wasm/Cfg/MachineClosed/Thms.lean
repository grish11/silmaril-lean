module

public import Silmaril.Wasm.Cfg.Machine.Thms
public import Silmaril.Wasm.Abstract.RegionCall.Thms

@[expose] public section

/-!
# The block-CFG machine with the checked closed oracle, against Core 3.0

The machine with calls (`MStepC`) instantiated with the actual oracle `Abstract.closedCallOk`:
calls answered by the closed native semantics (`closedCall`, the least fixpoint of running
callees), restricted to arity-checked stores (`StoreChk`) and typed invocations (`InvokeOk`).
`Abstract.callSound_closedCallOk` proves it Core-sound (`Region.CallSound`) for every profile and
host, so the machine's Core soundness holds with **no oracle hypothesis**:

* **`core_sound_closed`**: a run of the machine with `closedCallOk` from the CFG entry to a sink
  is a Core 3.0 run of the body to a final form of a region outcome the sink completes
  (`EndsC`).

* `callSoundA_closedCallOk`: `closedCallOk` is sound for every `call_ref` annotation
  (`Region.CallSoundA`, from `Abstract.callSoundAnn_closedCallOk`).
* **`frame_tail_closed`**: a run of the machine with `closedCallOk` from the CFG entry that ends
  by a tail call is a Core 3.0 run of the function's `FRAME` to the sink's code (frame
  replacement), with no oracle hypothesis.

Not claimed here: completeness for Core runs (Core to the machine needs callee adequacy).
-/

namespace Silmaril.Wasm.Cfg.Machine

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H} {body : Expr}

/-- **Core soundness of the machine with the checked closed oracle**, every profile and host,
no oracle hypothesis: a run from the CFG entry to a sink is a Core 3.0 run of the body to a final
form of the region outcome the sink completes. -/
theorem core_sound_closed {s : Store H} {f : Frame} {st' : MState H}
    (h : Relation.ReflTransGen (MStepC P host Abstract.closedCallOk body) (initial body s f) st')
    (hs : st'.node.IsSink) :
    ∃ o s₂ f₂ c', EndsC Abstract.closedCallOk st' s₂ f₂ o ∧
      Steps P host ⟨s, f, expression body⟩ ⟨s₂, f₂, c'⟩ ∧ o.Ends c' :=
  core_sound_initialC (Abstract.callSound_closedCallOk P host) h hs

/-- The checked closed oracle is Core-sound for every `call_ref` annotation. -/
theorem callSoundA_closedCallOk (P : Profile) (host : HostSemantics H) :
    Region.CallSoundA P host (Abstract.closedCallOk (H := H)) :=
  fun s s₁ f a fi ps rs us fl c hc hfi hty hn hcall =>
    Abstract.callSoundAnn_closedCallOk P host s s₁ f a fi ps rs us fl c hc hfi hty hn hcall

/-- **Tail calls at the frame with the checked closed oracle**, no oracle hypothesis: a run from
the CFG entry ending by a tail call is a Core 3.0 run of `FRAME_n{fi} (LABEL_n{} body)`, in any
outer frame, to the code of the sink the machine reached. -/
theorem frame_tail_closed {s : Store H} {fi : Frame} {st' : MState H} {s₂ : Store H}
    {f₂ : Frame} {W : List Val} {a : Nat} {c : Admin}
    (hE : EndsC Abstract.closedCallOk st' s₂ f₂ (.tail W a c))
    (hR : Region.RunC P host Abstract.closedCallOk s fi [] (expression body) s₂ f₂ (.tail W a c))
    (n : Nat) (f : Frame) {X : List Admin} (hX : codeOf body st' = some X) :
    Steps P host ⟨s, f, [.frame n fi [.label n [] (expression body)]]⟩ ⟨st'.store, f, X⟩ :=
  frame_tail_initialC (callSoundA_closedCallOk P host) hE hR n f hX

end Silmaril.Wasm.Cfg.Machine
