module

public import Silmaril.Wasm.Examples.JsonAccept.Instance.Thms
public import Silmaril.Wasm.Logic.Total.Thms
public import Silmaril.Wasm.Game.Accept.Export.Thms
import Silmaril.Proofs.Wasm.Examples.JsonAccept.Total

/-! # The JSON-subset acceptor: total correctness and exact acceptance

Total correctness of `accept` (the loop variant is `len - i`), proved with the total logic of
`Silmaril.Wasm.Logic.Total`. The loop rule with a variant (`Silmaril.Wasm.Logic.Words.t_while`)
is combined with the generator's total soundness for the loop-free body and for the code after
the loop (`Silmaril.Wasm.Logic.VC.wpc_sound_total`).

* **`accept_total`**: a total function specification (`TFSpecAt`): from any store and admitted
  arguments, **every** run of the call terminates, and it terminates returning the automaton's
  answer with the store unchanged.
* **`accept_exists`**: hence **some** run of `$invoke` returns that answer. This is an existence
  proof of a successful execution, not a never-reject statement.
* **Exact acceptance of the embedded module**, for every profile and every set of host relations
  containing at least one host (`exportAccepted_eq`, `exportRejected_eq`):

  `exportAccepted P Hosts prog "accept" = {w | w ∈ intText ∧ w.length < 2 ^ 32}`

  `exportRejected P Hosts prog "accept" = {w | w ∉ intText ∧ w.length < 2 ^ 32}`

  The bound `< 2 ^ 32` is the ABI's: the length is an `i32` and the segment may not wrap the
  address space. Inputs of every admitted length are decided, and the embedded acceptor is sound
  for JSON (`exportAccepted_subset_json`). The subset is `intText` (one integer with whitespace),
  **not all of JSON**: every other JSON text is rejected.

* **The combined reading** (`exportAcceptedNotRejected_eq`, `acceptsSafely_eq`): some run
  answers `1` and no run answers `0`, over the same runs and hosts, exactly on the same set.
  Accepted inputs are never also rejected (`exportAccepted_disjoint_rejected`).

The embedding is that of `Silmaril.Wasm.Game.Accept.Export`: the spec instance (unique,
`spec_instance_eq`), the input written into memory `0`, `accept(ptr, len)` invoked.
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.JsonAccept

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Verify Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
open Silmaril.Wasm.Numerics (Profile)

/-- **`accept` is totally correct.** -/
theorem accept_total {P : Profile} {host : HostSemantics Nat} {fi : FuncInst Nat} {a : Nat}
    {ps rs : Validation.Ty (.list .val)} (hcode : fi.code = .wasm prog.funcs[0])
    (he : Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 2) (hrs : rs.length = 1)
    (x : BitVec 32 × BitVec 32) : TFSpecAt P host a (spec.fspec fi a x) :=
  Silmaril.Proofs.Wasm.Examples.JsonAccept.accept_total hcode he hps hrs x

/-- **Some run of `accept` returns the automaton's answer**, store unchanged. -/
theorem accept_exists {P : Profile} {host : HostSemantics Nat} {s : Store Nat} {a : Nat}
    {fi : FuncInst Nat} {ps rs : Validation.Ty (.list .val)} (hfi : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm prog.funcs[0]) (he : Validation.Expand fi.type (.func ps rs))
    (hps : ps.length = 2) (hrs : rs.length = 1) {ma : Nat} {mt : MemoryType} {B : ByteArray}
    (hmem : MemAt s fi.module ma mt B) {p n : BitVec 32} (hb : p.toNat + n.toNat ≤ B.size)
    (hov : p.toNat + n.toNat < 2 ^ 32) :
    ∃ f', Steps P host (invoke s a [.i32 p, .i32 n]) ⟨s, f', vals [.i32 (if 2 ≤ runN 0
      (bytesN B p.toNat n.toNat) ∧ runN 0 (bytesN B p.toNat n.toNat) ≤ 4 then 1 else 0)]⟩ :=
  Silmaril.Proofs.Wasm.Examples.JsonAccept.accept_exists hfi hcode he hps hrs hmem hb hov

/-- **Exact acceptance**: the embedded module accepts exactly the integer texts shorter than
`2 ^ 32`. -/
theorem exportAccepted_eq {P : Profile} {Hosts : Set (HostSemantics Nat)}
    {host : HostSemantics Nat} (hh : host ∈ Hosts) :
    exportAccepted P Hosts prog "accept" = {w | w ∈ intText ∧ w.length < 2 ^ 32} := by
  ext w
  constructor
  · intro hw
    exact ⟨exportAccepted_subset_intText P Hosts hw,
      Silmaril.Proofs.Wasm.Examples.JsonAccept.exportAnswered_length hw⟩
  · rintro ⟨hi, hl⟩
    have h := Silmaril.Proofs.Wasm.Examples.JsonAccept.exportAnswered_of_run (P := P) hh hl
    have h1 : (if 2 ≤ runN 0 (w.map UInt8.toNat) ∧ runN 0 (w.map UInt8.toNat) ≤ 4
        then (1 : BitVec 32) else 0) = 1 :=
      ite_eq_left_iff.2 fun h' => absurd ((acc_iff w).2 hi) h'
    rw [h1] at h
    exact h

/-- **Exact rejection**: the embedded module rejects exactly the other strings shorter than
`2 ^ 32`. -/
theorem exportRejected_eq {P : Profile} {Hosts : Set (HostSemantics Nat)}
    {host : HostSemantics Nat} (hh : host ∈ Hosts) :
    exportRejected P Hosts prog "accept" = {w | w ∉ intText ∧ w.length < 2 ^ 32} := by
  ext w
  constructor
  · intro hw
    refine ⟨fun hi => ?_, Silmaril.Proofs.Wasm.Examples.JsonAccept.exportAnswered_length hw⟩
    exact absurd ((exportAnswered_iff hw).2 hi) (by decide)
  · rintro ⟨hi, hl⟩
    have h := Silmaril.Proofs.Wasm.Examples.JsonAccept.exportAnswered_of_run (P := P) hh hl
    have h0 : (if 2 ≤ runN 0 (w.map UInt8.toNat) ∧ runN 0 (w.map UInt8.toNat) ≤ 4
        then (1 : BitVec 32) else 0) = 0 :=
      ite_eq_right_iff.2 fun h' => absurd ((acc_iff w).1 h') hi
    rw [h0] at h
    exact h

/-- Accepted and rejected inputs partition the admitted strings. -/
theorem exportAccepted_union_rejected {P : Profile} {Hosts : Set (HostSemantics Nat)}
    {host : HostSemantics Nat} (hh : host ∈ Hosts) :
    exportAccepted P Hosts prog "accept" ∪ exportRejected P Hosts prog "accept" =
      {w | w.length < 2 ^ 32} := by
  rw [exportAccepted_eq hh, exportRejected_eq hh]
  ext w
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  tauto

/-- No input is both accepted and rejected. -/
theorem exportAccepted_disjoint_rejected {P : Profile} {Hosts : Set (HostSemantics Nat)}
    {host : HostSemantics Nat} (hh : host ∈ Hosts) :
    Disjoint (exportAccepted P Hosts prog "accept") (exportRejected P Hosts prog "accept") := by
  rw [exportAccepted_eq hh, exportRejected_eq hh]
  exact Set.disjoint_left.2 fun _ ha hr => hr.1 ha.1

/-- **Accepted and never rejected**: exactly the integer texts shorter than `2 ^ 32`. -/
theorem exportAcceptedNotRejected_eq {P : Profile} {Hosts : Set (HostSemantics Nat)}
    {host : HostSemantics Nat} (hh : host ∈ Hosts) :
    exportAcceptedNotRejected P Hosts prog "accept" = {w | w ∈ intText ∧ w.length < 2 ^ 32} := by
  rw [exportAcceptedNotRejected, Set.inter_eq_left.2
    (Set.subset_compl_iff_disjoint_right.2 (exportAccepted_disjoint_rejected hh)),
    exportAccepted_eq hh]

/-- The same, as the generic combined verdict `Silmaril.Accept.acceptsSafely`. -/
theorem acceptsSafely_eq {P : Profile} {Hosts : Set (HostSemantics Nat)}
    {host : HostSemantics Nat} (hh : host ∈ Hosts) :
    Silmaril.Accept.acceptsSafely (exportRun P Hosts prog "accept") {1} {0} =
      {w | w ∈ intText ∧ w.length < 2 ^ 32} := by
  rw [← exportAcceptedNotRejected_eq_acceptsSafely, exportAcceptedNotRejected_eq hh]

end Silmaril.Wasm.Examples.JsonAccept
