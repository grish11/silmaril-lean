module

public import Silmaril.Wasm.Institution.Operational.LegacyDivision.V1.Defs
public import Silmaril.Wasm.Institution.Operational.LegacyDivision.Core.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.LegacyDivision.V1

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.LegacyDivision.V1

open CategoryTheory Silmaril.Logic.Operational
open Silmaril.Wasm.V1.Execution
open Silmaril.Wasm.Execution.Runtime (Frame)

theorem pure_iff {xs ys : List Admin} (ready : Supported xs) :
    Redex scalarSyntax xs ys ↔ PureStep xs ys :=
  ⟨Proofs.pure_sound, fun h => Proofs.pure_readback h ready⟩

variable {H : Type} {host : HostSemantics H} {a b : Config H}

theorem step_sound (s : Store H) (f : Frame) {xs ys : List Admin} (h : Derives xs ys) :
    Step host ⟨s, f, xs⟩ ⟨s, f, ys⟩ :=
  Proofs.step_sound s f h

theorem step_readback (ready : Supported a.code) (h : Step host a b) :
    Derives a.code b.code ∧ a.store = b.store ∧ a.frame = b.frame :=
  Proofs.step_readback h ready

theorem step_closed (ready : Supported a.code) (h : Step host a b) : Supported b.code :=
  (derives_admitted (step_readback ready h).1).2

theorem steps_iff (ready : Supported a.code) :
    Steps host a b ↔ DerivesPath scalarSyntax a.code b.code ∧ a.store = b.store ∧ a.frame = b.frame :=
  ⟨fun h => Proofs.steps_readback h ready,
    fun ⟨h, hs, hf⟩ => Proofs.steps_sound h hs hf⟩

@[simp] theorem decode_encode (a : Config H) : decode (encode a) = a := rfl

@[simp] theorem encode_decode (a : (WasmShape.signatures.obj (nativeShape H)).State) :
    encode (decode a) = a := rfl

theorem atom_iff (host : HostSemantics H) (ready : Supported a.code) :
    (WasmShape.institution.obj (nativeShape H)).Sat (Discrete.mk (nativeSystem host).model)
        (encode a, (), encode b) ↔
      Derives a.code b.code ∧ a.store = b.store ∧ a.frame = b.frame :=
  ⟨fun h => step_readback ready h.2, fun ⟨h, hs, hf⟩ =>
    ⟨ready, Proofs.edge_sound h hs hf⟩⟩

end Silmaril.Wasm.Institution.Operational.LegacyDivision.V1
