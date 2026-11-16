module

public import Silmaril.Wasm.Examples.MemberCheck.Defs
public import Silmaril.Wasm.Verify.FnSpec.Thms
public import Silmaril.Wasm.Logic.Total.Thms
public import Silmaril.Wasm.Binaryen.Exe.EncodeSound
public import Silmaril.Wasm.Verify.Kernel.Defs
public import Silmaril.Logic.Consequence.Structural.Defs
import Silmaril.Proofs.Wasm.Examples.MemberCheck.Basic

/-! # The finite membership checker as a core Wasm module: theorems

An **actual core Wasm module**, verified against Core 3.0 small-step execution at every numerics
profile and every host relation. A query is a byte string: the first byte is the statement, and
the rest are the assumptions.

* **Bytes**: the encoder produces the 108-byte `bytes` (`encodeModule_eq`). They encode `prog` in
  the specification's binary grammar (`bytes_encodes`) and decode back to it (`decode_bytes`).
* **The function**: `check` meets `spec` (`check_verified`). Every returning run answers
  membership (`check_returns`). It is totally correct: the loop variant is `len - i`, and some run
  returns (`check_exists`).
* **The instance**: it exists and is unique (`isSpecInstance`, `spec_instance_eq`).
* **Exact acceptance** in the embedding of `Silmaril.Wasm.Game.Accept.Export`:
  `exportAccepted P Hosts prog "check" = {w | w ∈ memberLang ∧ w.length < 2 ^ 32}` and
  `exportRejected … = {w | w ∉ memberLang ∧ w.length < 2 ^ 32}`, for every host set containing a
  host (`exportAccepted_eq`, `exportRejected_eq`). Accepted inputs are in `memberLang` for every
  host set (`exportAccepted_subset`).
* **As a consequence checker** (`Silmaril.Logic.Consequence.Structural`): encode a query
  `(as, c)` as `c :: as`. The module's relation on byte lists is exactly membership
  (`accepted_iff_mem`). It is therefore `Reflexive` and contained in every reflexive relation
  (`reflexive_accepted`, `accepted_le_of_reflexive`), for assumption lists shorter than
  `2 ^ 32 - 1` bytes.

**Scope.** Statements and assumptions are single bytes. No component wraps this module: the
canonical-ABI correspondence to `Silmaril.Wasi.Consequence.exportCheck` is not established, and
no compilation correctness is claimed.
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.MemberCheck

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Verify Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Validation (CModuleType)
open Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
open Silmaril.Wasm.Examples.JsonAccept (bytesN)
open Silmaril.Wasm.Numerics (Profile)

/-! ## Bytes -/

theorem encodeModule_eq : Binaryen.Exe.encodeModule? prog = .ok bytes := by kernel_rfl

/-- **`bytes` encodes `prog`** in the specification's binary grammar. -/
theorem bytes_encodes : Binary.Core.Encodes bytes prog :=
  Binaryen.Exe.encodeModule?_sound encodeModule_eq

theorem decode_bytes : Binary.Core.decode? ⟨bytes.toArray⟩ = some prog := by kernel_rfl

/-! ## The function -/

/-- **`check` meets its specification.** -/
theorem check_verified : Verified prog 0 spec :=
  ⟨_, rfl, Silmaril.Proofs.Wasm.Examples.MemberCheck.spec_vc⟩

/-- `memb` on byte values is membership in `memberLang`. -/
theorem memb_iff (w : List UInt8) : memb (w.map UInt8.toNat) = true ↔ w ∈ memberLang :=
  Silmaril.Proofs.Wasm.Examples.MemberCheck.memb_iff w

variable {P : Profile} {host : HostSemantics Nat} {s : Store Nat} {a : Nat} {fi : FuncInst Nat}
  {ps rs : Validation.Ty (.list .val)} {ma : Nat} {mt : MemoryType} {B : ByteArray}
  {p n : BitVec 32}

/-- **Every returning run of `check` answers membership**, store unchanged. -/
theorem check_returns (hfi : s.funcs[a]? = some fi) (hc : fi.code = .wasm prog.funcs[0])
    (he : Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 2) (hrs : rs.length = 1)
    (hmem : MemAt s fi.module ma mt B) (hb : p.toNat + n.toNat ≤ B.size)
    (hov : p.toNat + n.toNat < 2 ^ 32) {s' : Store Nat} {f' : Frame} {res : List Val}
    (hs : Steps P host (invoke s a [.i32 p, .i32 n]) ⟨s', f', vals res⟩) :
    s' = s ∧ res = [.i32 (if memb (bytesN B p.toNat n.toNat) then 1 else 0)] :=
  Silmaril.Proofs.Wasm.Examples.MemberCheck.check_returns hfi hc he hps hrs hmem hb hov hs

/-- **Some run of `check` returns**, with that answer. -/
theorem check_exists (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm prog.funcs[0])
    (he : Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 2) (hrs : rs.length = 1)
    (hmem : MemAt s fi.module ma mt B) (hb : p.toNat + n.toNat ≤ B.size)
    (hov : p.toNat + n.toNat < 2 ^ 32) :
    ∃ f', Steps P host (invoke s a [.i32 p, .i32 n])
      ⟨s, f', vals [.i32 (if memb (bytesN B p.toNat n.toNat) then 1 else 0)]⟩ :=
  Silmaril.Proofs.Wasm.Examples.MemberCheck.check_exists hfi hcode he hps hrs hmem hb hov

/-! ## The instance and the embedding -/

theorem isSpecInstance : IsSpecInstance prog specMT specInst specPrep.1 :=
  Silmaril.Proofs.Wasm.Examples.MemberCheck.isSpecInstance

theorem spec_instance_eq {mt : CModuleType} {I : ScalarInstance} {c₀ : Config Nat}
    (hI : IsSpecInstance prog mt I c₀) : mt = specMT ∧ c₀ = specPrep.1 :=
  Silmaril.Proofs.Wasm.Examples.MemberCheck.spec_instance_eq hI

/-- What the embedded module accepts is in `memberLang`, for every host set. -/
theorem exportAccepted_subset (P : Profile) (Hosts : Set (HostSemantics Nat)) :
    exportAccepted P Hosts prog "check" ⊆ memberLang := fun w hw => by
  have := Silmaril.Proofs.Wasm.Examples.MemberCheck.exportAnswered_eq hw
  by_cases h : w ∈ memberLang
  · exact h
  · simp only [h, ↓reduceIte] at this; exact absurd this (by decide)

/-- **Exact acceptance.** -/
theorem exportAccepted_eq (P : Profile) {Hosts : Set (HostSemantics Nat)} (hH : Hosts.Nonempty) :
    exportAccepted P Hosts prog "check" = {w | w ∈ memberLang ∧ w.length < 2 ^ 32} := by
  ext w
  refine ⟨fun hw => ⟨exportAccepted_subset P Hosts hw,
    Silmaril.Proofs.Wasm.Examples.MemberCheck.exportAnswered_length hw⟩, fun ⟨hm, hl⟩ => ?_⟩
  have := Silmaril.Proofs.Wasm.Examples.MemberCheck.exportAnswered_of_run (P := P)
    hH.choose_spec hl
  simp only [hm, ↓reduceIte] at this
  exact this

/-- **Exact rejection.** -/
theorem exportRejected_eq (P : Profile) {Hosts : Set (HostSemantics Nat)} (hH : Hosts.Nonempty) :
    exportRejected P Hosts prog "check" = {w | w ∉ memberLang ∧ w.length < 2 ^ 32} := by
  ext w
  constructor
  · intro hw
    have h := Silmaril.Proofs.Wasm.Examples.MemberCheck.exportAnswered_eq hw
    refine ⟨fun hm => ?_, Silmaril.Proofs.Wasm.Examples.MemberCheck.exportAnswered_length hw⟩
    simp only [hm, ↓reduceIte] at h; exact absurd h (by decide)
  · rintro ⟨hm, hl⟩
    have := Silmaril.Proofs.Wasm.Examples.MemberCheck.exportAnswered_of_run (P := P)
      hH.choose_spec hl
    simp only [hm, ↓reduceIte] at this
    exact this

/-! ## As a consequence checker -/

/-- The module's relation on byte assumptions and statements: `c :: as` is accepted. -/
def accepted (P : Profile) (Hosts : Set (HostSemantics Nat)) :
    Silmaril.Consequence.Structural.Rel UInt8 :=
  fun as c => c :: as ∈ exportAccepted P Hosts prog "check"

/-- **The module's relation is membership**, below the ABI bound. -/
theorem accepted_iff_mem (P : Profile) {Hosts : Set (HostSemantics Nat)} (hH : Hosts.Nonempty)
    {as : List UInt8} (hl : as.length + 1 < 2 ^ 32) (c : UInt8) :
    accepted P Hosts as c ↔ c ∈ as := by
  rw [accepted, exportAccepted_eq P hH]
  simp only [Set.mem_ofPred_eq, List.length_cons, hl, and_true]
  exact ⟨fun ⟨_, _, h, hm⟩ => by cases h; exact hm, fun h => ⟨c, as, rfl, h⟩⟩

/-- **Reflexive**, below the ABI bound. -/
theorem reflexive_accepted (P : Profile) {Hosts : Set (HostSemantics Nat)} (hH : Hosts.Nonempty)
    {as : List UInt8} (hl : as.length + 1 < 2 ^ 32) {c : UInt8} (h : c ∈ as) :
    accepted P Hosts as c :=
  (accepted_iff_mem P hH hl c).2 h

/-- **Contained in every reflexive relation**, for every host set. -/
theorem accepted_le_of_reflexive (P : Profile) (Hosts : Set (HostSemantics Nat))
    {target : Silmaril.Consequence.Structural.Rel UInt8}
    (ht : Silmaril.Consequence.Structural.Reflexive target) {as : List UInt8} {c : UInt8}
    (h : accepted P Hosts as c) : target as c := by
  obtain ⟨_, _, he, hm⟩ := exportAccepted_subset P Hosts h
  cases he
  exact ht hm

end Silmaril.Wasm.Examples.MemberCheck
