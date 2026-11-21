module

public import Silmaril.Wasm.Execution.Core.Entry.Determinism.Defs
public import Silmaril.Semantics.Operational.Determinism.Fuel.Thms
public import Silmaril.Wasm.Execution.Core.Intrinsic.OpSem.Thms
import Silmaril.Proofs.Wasm.Execution.Core.Entry.Determinism

public section

namespace Silmaril.Wasm.Execution.Core.Entry

open Numerics Semantics.Operational SingleThreaded SingleThreaded.Det SingleThreaded.Exec Cfg.ProfileFree

variable {H : Type} {P : Profile} {host : HostSemantics H}

def driverOracle (head : HeadFn H)
    (sound : ∀ ⦃source target⦄, step? head source = some target → Step P host source target) :
    Oracle (WithUB.ofOpSem (ordinary P host)) :=
  ⟨driverDecision head, Proofs.Wasm.Execution.Core.Entry.Determinism.driver_valid head sound⟩

@[simp] theorem driverOracle_pick (head : HeadFn H)
    (sound : ∀ ⦃source target⦄, step? head source = some target → Step P host source target) (source : Config H) :
    (driverOracle head sound).pick source = driverDecision head source := by unfold driverOracle; rfl

/-- The actual deterministic numeric profile plus no host answers has unique
finite results under raw `Step`; this is not primitive-step uniqueness. -/
theorem deterministic_result (oracle : GrowOracle) (source : Config H) :
    (ordinary (profile oracle) (noHost : HostSemantics H)).ResultDetAt source :=
  Proofs.Wasm.Execution.Core.Entry.Determinism.deterministic_result oracle source

/-- Profile-free configurations transfer an entire host-free Core path,
for every actual numeric profile pair. This is not a host-schedule theorem. -/
theorem profileFree_steps {Q : Profile} {source target : Config H}
    (free : ConfigFree source) (path : Steps P noHost source target) : Steps Q noHost source target :=
  Proofs.Wasm.Execution.Core.Entry.Determinism.profileFree_steps free path

theorem profileFree_result (source : Config H) (free : ConfigFree source) :
    (ordinary P (noHost : HostSemantics H)).ResultDetAt source :=
  Proofs.Wasm.Execution.Core.Entry.Determinism.profileFree_result source free

end Silmaril.Wasm.Execution.Core.Entry

namespace Silmaril.Wasm.Execution.Core.Intrinsic

open Numerics Validation Semantics.Operational SingleThreaded

variable {H : Type} {context : Context} {world : World H context} {locals results : List IntType}

def normalOracle : Oracle (typedSem (world := world) (locals := locals) (results := results)) :=
  ⟨normalDecision, Proofs.Wasm.Execution.Core.Entry.Determinism.normal_valid⟩

@[simp] theorem normalOracle_pick (source : State world locals results) :
    normalOracle.pick source = normalDecision source := by unfold normalOracle; rfl

/-- Finite equivalence with actual Core on the landed intrinsic fragment, not
with arbitrary raw starts or with equal primitive step budgets. -/
theorem State.raw_may_iff_bounded (state : State world locals results) (oracle : GrowOracle)
    (outcome : Outcome Completion) : (rawSem oracle (stackTypes results)).toOpSem.May state.erase outcome ↔
      ∃ fuel final, normalOracle.run state fuel = .stop final (.observed outcome) :=
  (state.may_iff outcome).trans (normalOracle.may_iff_run state outcome state.typed_deterministic
    Proofs.Wasm.Execution.Core.Entry.Determinism.normal_terminal (WithUB.ofOpSem_safe _ _)
    (fun {source} _ => Proofs.Wasm.Execution.Core.Entry.Determinism.normal_known source))

end Silmaril.Wasm.Execution.Core.Intrinsic
