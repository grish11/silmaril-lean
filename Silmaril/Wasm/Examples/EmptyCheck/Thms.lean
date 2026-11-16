module

public import Silmaril.Wasm.Examples.EmptyCheck.Defs
public import Silmaril.Wasm.Verify.FnSpec.Thms
public import Silmaril.Wasm.Logic.Total.Thms
public import Silmaril.Wasm.Binaryen.Exe.EncodeSound
public import Silmaril.Wasm.Verify.Kernel.Defs
public import Silmaril.Logic.Consequence.Defs
import Silmaril.Proofs.Wasm.Examples.EmptyCheck.Basic

/-! # The empty checker as a core Wasm module: theorems

An **actual core Wasm module**, verified against Core 3.0 small-step execution
(`Execution.Core.Steps`) at every numerics profile and every host relation. The theorems are
about the module value `prog` and its 45-byte binary `bytes`. They are not about a component.

* **Bytes**: silmaril-lean's encoder produces `bytes` from `prog` (`encodeModule_eq`), and these
  bytes satisfy the specification's binary grammar for `prog` (`bytes_encodes`,
  `encodeModule?_sound`). The decoder maps them back to `prog` (`decode_bytes`).
* **The function**: `check` meets `spec` (`check_verified`). Every returning run returns `0` with
  the store unchanged (`check_returns`), and some run returns (`check_exists`, total correctness
  of the loop-free body).
* **The instance**: `prog` has a spec instance (`isSpecInstance`), and it is unique
  (`spec_instance_eq`).
* **The embedding** (`Silmaril.Wasm.Game.Accept.Export`: spec instance, input written into memory
  `0`, `check(ptr, len)` invoked):
  * `exportAccepted_eq_empty`: nothing is accepted, for every profile and host set;
  * `exportRejected_eq`: every input shorter than `2 ^ 32` is rejected, for every host set
    containing a host.
* **As a consequence checker** (`Silmaril.Logic.Consequence`): for any byte encoding `enc` of
  assumptions and statements, the relation "`enc x c` is accepted" is empty
  (`accepted_system_eq_bot`). It is sound for every target (`sound_any`), and complete only for
  the empty one.

**Scope.** No component wraps this module here. A component exporting `check(ax, stmt) -> bool`
over it would need the canonical-ABI lowering between the component's `list<u8>` arguments and
the module's `(ptr, len)` (a `CanonLowerAccept`-style correspondence). That correspondence is not
established, so the component reading `Silmaril.Wasi.Consequence.exportCheck` is not connected
to this module. No compilation correctness is claimed.
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.EmptyCheck

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Verify Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Validation (CModuleType)
open Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
open Silmaril.Wasm.Numerics (Profile)

/-! ## Bytes -/

/-- The encoder produces `bytes`. -/
theorem encodeModule_eq : Binaryen.Exe.encodeModule? prog = .ok bytes := by kernel_rfl

/-- **`bytes` encodes `prog`** in the specification's binary grammar. -/
theorem bytes_encodes : Binary.Core.Encodes bytes prog :=
  Binaryen.Exe.encodeModule?_sound encodeModule_eq

/-- The decoder maps `bytes` back to `prog`. -/
theorem decode_bytes : Binary.Core.decode? ⟨bytes.toArray⟩ = some prog := by kernel_rfl

/-! ## The function -/

/-- **`check` meets its specification.** -/
theorem check_verified : Verified prog 0 spec :=
  ⟨_, rfl, Silmaril.Proofs.Wasm.Examples.EmptyCheck.spec_vc⟩

variable {P : Profile} {host : HostSemantics Nat} {s : Store Nat} {a : Nat} {fi : FuncInst Nat}
  {ps rs : Validation.Ty (.list .val)} {ma : Nat} {mt : MemoryType} {B : ByteArray}
  {p n : BitVec 32}

/-- **Every returning run of `check` returns `0`**, store unchanged. -/
theorem check_returns (hfi : s.funcs[a]? = some fi) (hc : fi.code = .wasm prog.funcs[0])
    (he : Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 2) (hrs : rs.length = 1)
    (hmem : MemAt s fi.module ma mt B) (hb : p.toNat + n.toNat ≤ B.size)
    (hov : p.toNat + n.toNat < 2 ^ 32) {s' : Store Nat} {f' : Frame} {res : List Val}
    (hs : Steps P host (invoke s a [.i32 p, .i32 n]) ⟨s', f', vals res⟩) :
    s' = s ∧ res = [.i32 0] :=
  Silmaril.Proofs.Wasm.Examples.EmptyCheck.check_returns hfi hc he hps hrs hmem hb hov hs

/-- **Some run of `check` returns `0`.** -/
theorem check_exists (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm prog.funcs[0])
    (he : Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 2) (hrs : rs.length = 1)
    (hmem : MemAt s fi.module ma mt B) (hb : p.toNat + n.toNat ≤ B.size)
    (hov : p.toNat + n.toNat < 2 ^ 32) :
    ∃ f', Steps P host (invoke s a [.i32 p, .i32 n]) ⟨s, f', vals [.i32 0]⟩ :=
  Silmaril.Proofs.Wasm.Examples.EmptyCheck.check_exists hfi hcode he hps hrs hmem hb hov

/-! ## The instance and the embedding -/

/-- `prog` has a spec instance (the embedding is not vacuous). -/
theorem isSpecInstance : IsSpecInstance prog specMT specInst specPrep.1 :=
  Silmaril.Proofs.Wasm.Examples.EmptyCheck.isSpecInstance

/-- Every spec instance of `prog` is that one. -/
theorem spec_instance_eq {mt : CModuleType} {I : ScalarInstance} {c₀ : Config Nat}
    (hI : IsSpecInstance prog mt I c₀) : mt = specMT ∧ c₀ = specPrep.1 :=
  Silmaril.Proofs.Wasm.Examples.EmptyCheck.spec_instance_eq hI

/-- **Nothing is accepted.** -/
theorem exportAccepted_eq_empty (P : Profile) (Hosts : Set (HostSemantics Nat)) :
    exportAccepted P Hosts prog "check" = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hw =>
    absurd (Silmaril.Proofs.Wasm.Examples.EmptyCheck.exportAnswered_zero hw) (by decide)

/-- **Every admitted input is rejected**, for a host set containing a host. -/
theorem exportRejected_eq (P : Profile) {Hosts : Set (HostSemantics Nat)} (hH : Hosts.Nonempty) :
    exportRejected P Hosts prog "check" = {w | w.length < 2 ^ 32} := by
  ext w
  exact ⟨Silmaril.Proofs.Wasm.Examples.EmptyCheck.exportAnswered_length,
    fun hw => Silmaril.Proofs.Wasm.Examples.EmptyCheck.exportAnswered_of_run hH.choose_spec hw⟩

/-! ## As a consequence checker -/

/-- **For any byte encoding, the module's consequence relation is empty.** -/
theorem accepted_system_eq_bot {X C : Type} (enc : X → C → List UInt8) (P : Profile)
    (Hosts : Set (HostSemantics Nat)) :
    (fun x c => enc x c ∈ exportAccepted P Hosts prog "check" :
      Silmaril.Consequence.System X C) = ⊥ := by
  funext x c
  simp [exportAccepted_eq_empty]

/-- It is sound for every target system. -/
theorem sound_any {X C : Type} (enc : X → C → List UInt8) (P : Profile)
    (Hosts : Set (HostSemantics Nat)) (target : Silmaril.Consequence.System X C) :
    Silmaril.Consequence.System.Sound
      (fun x c => enc x c ∈ exportAccepted P Hosts prog "check") target := by
  rw [accepted_system_eq_bot]; exact bot_le

end Silmaril.Wasm.Examples.EmptyCheck
