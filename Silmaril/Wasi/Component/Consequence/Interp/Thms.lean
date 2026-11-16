module

public import Silmaril.Wasi.Component.Consequence.Interp.Defs
public import Silmaril.Wasi.Component.Consequence.Signed.Thms
public import Silmaril.Logic.Consequence.Interp.Thms
public import Silmaril.Wasm.Verify.Kernel.Defs

/-! # Protocol readings as interpretations: theorems

* The trace readings are always defined, and their raw systems are the protocol relations
  (`batchInterp_eq`, `seqInterp_eq`, `assumeAssertSeqInterp_eq`).
* **Bytes**: the registered bytes of `MemberCheck` decode, and read as `coreSeq` of its module
  (`coreBytesInterp_member`). Under `memberConfig` the system is sound against single-succedent
  membership for every host set (`member_sound`), and complete on the slice
  `Γ.length + 1 < 2 ^ 32` for a nonempty host set (`member_completeOn`). The bytes of `EmptyCheck`
  read as `some ⊥`, a verified empty system (`coreBytesInterp_empty`). Bytes that do not decode
  read as `none`, which is not a system (`coreBytesInterp_nil`).
-/

@[expose] public section

namespace Silmaril.Wasi.Consequence

open Silmaril.Consequence (Interp System Signed)
open Silmaril.Wasm.Component (Val)

variable {V : Type}

theorem batchInterp_eq (decV : List Val → Option V) (e : BatchConfig) (T : Set (List WEv)) :
    batchInterp decV e T = some (Accepted T (importBatch e.b e.fns decV e.td)) := rfl

theorem seqInterp_eq (decΓ decΔ : Val → Option (List V)) (f : FnName) (T : Set (List WEv)) :
    seqInterp decΓ decΔ f T = some (seqOf T (seqCheck f decΓ decΔ)) := rfl

theorem assumeAssertSeqInterp_eq (decV : List Val → Option V) (e : AssumeAssertConfig)
    (T : Set (List WEv)) :
    assumeAssertSeqInterp decV e T =
      some (pairSeqOf T (exportAssumeAssert e.b e.fns decV e.snap)) := rfl

/-- The bytes of `MemberCheck` read as `coreSeq` of its module. -/
theorem coreBytesInterp_member (e : CoreConfig) :
    coreBytesInterp e ⟨Silmaril.Wasm.Examples.MemberCheck.bytes.toArray⟩ =
      some (coreSeq e.P e.Hosts Silmaril.Wasm.Examples.MemberCheck.prog e.name e.enc) := by
  simp [coreBytesInterp, Interp.comap, Silmaril.Wasm.Examples.MemberCheck.decode_bytes,
    coreInterp]

/-- **Sound against single-succedent membership**, for every host set. -/
theorem member_sound (P : Silmaril.Wasm.Numerics.Profile)
    (Hosts : Set (Silmaril.Wasm.Execution.Core.HostSemantics Nat))
    {S : System (List UInt8) (List UInt8)}
    (h : coreBytesInterp (memberConfig P Hosts)
      ⟨Silmaril.Wasm.Examples.MemberCheck.bytes.toArray⟩ = some S) :
    S ≤ fun Γ Δ => ∃ c, Δ = [c] ∧ c ∈ Γ := by
  rw [coreBytesInterp_member] at h
  cases h
  exact fun Γ Δ => coreSeq_member_sound P Hosts

/-- **Complete on the ABI slice**, for a nonempty host set. -/
theorem member_completeOn (P : Silmaril.Wasm.Numerics.Profile)
    {Hosts : Set (Silmaril.Wasm.Execution.Core.HostSemantics Nat)} (hH : Hosts.Nonempty)
    {S : System (List UInt8) (List UInt8)}
    (h : coreBytesInterp (memberConfig P Hosts)
      ⟨Silmaril.Wasm.Examples.MemberCheck.bytes.toArray⟩ = some S) :
    S.CompleteOn (fun Γ Δ => ∃ c, Δ = [c] ∧ c ∈ Γ) fun Γ _ => Γ.length + 1 < 2 ^ 32 := by
  rw [coreBytesInterp_member] at h
  cases h
  exact fun Γ Δ hl hm => (coreSeq_member_iff P hH hl).2 hm

/-- **The bytes of `EmptyCheck` read as a verified empty system**, not as `none`. -/
theorem coreBytesInterp_empty (e : CoreConfig) (he : e.name = "check") :
    coreBytesInterp e ⟨Silmaril.Wasm.Examples.EmptyCheck.bytes.toArray⟩ = some ⊥ := by
  simp only [coreBytesInterp, Interp.comap, Silmaril.Wasm.Examples.EmptyCheck.decode_bytes,
    Option.bind_some, coreInterp, he, coreSeq_empty]

/-- Bytes that do not decode are not interpretable. -/
theorem coreBytesInterp_nil (e : CoreConfig) : coreBytesInterp e ByteArray.empty = none := by
  have : Silmaril.Wasm.Binary.Core.decode? ByteArray.empty = none := by kernel_rfl
  simp [coreBytesInterp, Interp.comap, this]

end Silmaril.Wasi.Consequence
