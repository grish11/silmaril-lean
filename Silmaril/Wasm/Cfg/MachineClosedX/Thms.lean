module

public import Silmaril.Wasm.Cfg.MachineClosedX.Defs
public import Silmaril.Wasm.Cfg.Machine.Thms
public import Silmaril.Wasm.Cfg.Region.Thms
import Silmaril.Proofs.Wasm.Cfg.CallClosedX

@[expose] public section

/-!
# The block-CFG machine with the typed closed extended oracle, against Core 3.0

Block bodies run direct, indirect and reference calls (`call`, `call_indirect`, `call_ref`:
`Region.RunC.call`, `callInd*`, `callRef*`, resolved by `CallRes.IndRes` and the reference on
the stack as `CallX.EvalOX` resolves them), every resolved call answered by the same oracle.
With the typed closed extended oracle `closedXOk` (no host, every profile):

* `callSoundA_closedXOk`: it is Core-sound for every `call_ref` form (`Region.CallSoundA`),
  from `Interp.OracleX.oracleSoundT_typedClosed`; it never throws (`Interp.FlowOk`).
* **`run_soundC_closedX`**: a region run with `closedXOk` is a Core 3.0 run to a final form of
  its outcome;
* **`core_sound_closedX`**: a machine run with `closedXOk` from the CFG entry to a sink is a Core
  3.0 run of the body to a final form of the outcome the sink completes;
* **`frame_tail_closedX`**: one ending by a tail call is a Core 3.0 run of the function's
  `FRAME` to the sink's code.

Soundness only. The region-level completeness theorems now cover `call_indirect`/`call_ref`
(`FragC` includes them), for any complete oracle; with `closedCallX` this needs its completeness
(`CallCompleteG`, the converse of the extended closure) and the discharge of its typing guard at
each call site, neither of which is claimed here.
-/

namespace Silmaril.Wasm.Cfg.Machine

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} {body : Expr}

/-- **The typed closed extended oracle is Core-sound for every `call_ref` form** (no host). -/
theorem callSoundA_closedXOk (P : Profile) :
    Region.CallSoundA P Interp.noHostX (closedXOk (H := H)) :=
  Proofs.Region.callSoundA_closedXOk P

/-- **Region runs with the typed closed extended oracle are Core 3.0 runs** (no host, every
profile): direct, indirect and reference calls included. -/
theorem run_soundC_closedX (P : Profile) {s s' : Store H} {f f' : Frame} {vs : List Val}
    {code : List Admin} {o : Region.Out}
    (h : Region.RunC P Interp.noHostX closedXOk s f vs code s' f' o) :
    ∃ c', Steps P Interp.noHostX ⟨s, f, vals vs ++ code⟩ ⟨s', f', c'⟩ ∧ o.Ends c' :=
  Region.run_soundC (callSoundA_closedXOk P) h

/-- **Core soundness of the machine with the typed closed extended oracle** (no host, every
profile, no oracle hypothesis): a run from the CFG entry to a sink is a Core 3.0 run of the body
to a final form of the region outcome the sink completes. -/
theorem core_sound_closedX (P : Profile) {s : Store H} {f : Frame} {st' : MState H}
    (h : Relation.ReflTransGen (MStepC P Interp.noHostX closedXOk body) (initial body s f) st')
    (hs : st'.node.IsSink) :
    ∃ o s₂ f₂ c', EndsC closedXOk st' s₂ f₂ o ∧
      Steps P Interp.noHostX ⟨s, f, expression body⟩ ⟨s₂, f₂, c'⟩ ∧ o.Ends c' :=
  core_sound_initialC (callSoundA_closedXOk P) h hs

/-- **Tail calls at the frame with the typed closed extended oracle** (no host): a machine run
from the CFG entry ending by a tail call is a Core 3.0 run of `FRAME_n{fi} (LABEL_n{} body)`, in
any outer frame, to the code of the sink the machine reached. -/
theorem frame_tail_closedX (P : Profile) {s : Store H} {fi : Frame} {st' : MState H}
    {s₂ : Store H} {f₂ : Frame} {W : List Val} {a : Nat} {c : Admin}
    (hE : EndsC closedXOk st' s₂ f₂ (.tail W a c))
    (hR : Region.RunC P Interp.noHostX closedXOk s fi [] (expression body) s₂ f₂ (.tail W a c))
    (n : Nat) (f : Frame) {X : List Admin} (hX : codeOf body st' = some X) :
    Steps P Interp.noHostX ⟨s, f, [.frame n fi [.label n [] (expression body)]]⟩
      ⟨st'.store, f, X⟩ :=
  frame_tail_initialC (callSoundA_closedXOk P) hE hR n f hX

end Silmaril.Wasm.Cfg.Machine
