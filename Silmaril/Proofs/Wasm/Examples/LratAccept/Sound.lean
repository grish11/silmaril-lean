module

public import Silmaril.Proofs.Wasm.Examples.LratAccept.Inst
public import Silmaril.Wasm.Acceptor.Alloc.Thms

@[expose] public section

/-!
# The acceptor's exports: every returning run

Function specifications of the three exported functions of the instantiated acceptor, from the
body proofs (`FSpecValid.of_body_hwp`), and their reading for every run of `$invoke`
(`FSpecValid.invoke_vals`):

* `checkStream_sound`, `checkNested_sound`: in every store with the instance's functions, any
  LRAT state (eight globals, a 64 KiB memory `0`), any heap pointer and a 1 MiB ABI memory `B₁`
  holding the arguments in bounds, a run of `check-stream` (`check-nested`) returning `[r]` with
  `r ≠ 0` puts the problem in `UnsatStream` (`UnsatNested`);
* `realloc_sound`: a returning run of `cabi_realloc` only sets the heap pointer, as `ReallocOk`
  says.

Every profile and host relation. A Silmaril addition.
-/

namespace Silmaril.Proofs.Wasm.Examples.LratAccept

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Examples.LRAT Silmaril.Wasm.Examples.Common
open Silmaril.Wasm.Examples.LratAccept
open Silmaril.Logic.SAT.Carrier

variable {P : Profile} {host : HostSemantics Nat}

theorem accStore_shape {s : Store Nat} {G : List (BitVec 32)} {B₀ : ByteArray} {top : BitVec 32}
    {B₁ : ByteArray} (h : AccStore s G B₀ top B₁) : Shape (accX top B₁) s G B₀ :=
  ⟨h.funcs, h.globals, h.len, h.mems, h.size₀⟩

theorem size_lt {B₁ : ByteArray} (h : B₁.size = memBytes) : B₁.size < 2 ^ 32 := by
  rw [h]; decide

/-- The specification of a check: the arguments, the store, a nonzero answer means `Goal`. -/
def checkSpec (args₀ : List Val) (top : BitVec 32) (B₁ : ByteArray) (Goal : Prop) : FSpec Nat where
  pre s args := args = args₀ ∧ ∃ G B₀, AccStore s G B₀ top B₁
  post _ _ s' o := checkPost Goal s' o

theorem prog_f11 : prog.funcs[11]? = some ⟨⟨3⟩, checkLocals, checkStreamBody⟩ := rfl
theorem prog_f12 : prog.funcs[12]? = some ⟨⟨3⟩, checkLocals, checkNestedBody⟩ := rfl

set_option maxHeartbeats 1000000 in
/-- `check-stream` meets its specification. -/
theorem checkStream_spec {top : BitVec 32} {B₁ : ByteArray} {pp pl cp cl : BitVec 32}
    (hpp : pp.toNat + 4 * pl.toNat ≤ memBytes) (hcp : cp.toNat + 4 * cl.toNat ≤ memBytes) :
    FSpecValid P host 11 (checkSpec [Val.i32 pp, Val.i32 pl, Val.i32 cp, Val.i32 cl] top B₁
      (wordsAt B₁ pp.toNat pl.toNat ∈ UnsatStream)) := by
  obtain ⟨fi, f, ty, hfi, hf, hty, hcode, hmod, hexp⟩ := acc_fn 11 (by decide)
  rw [prog_f11] at hf
  cases hf
  cases (show ty = ty4c from Option.some.inj (hty.symm.trans rfl))
  refine FSpecValid.of_body_hwp (fun s _ hpre => ?_) hcode hexp
    (fun _ _ hpre => by rw [hpre.1]; rfl) fun s args hpre => ?_
  · obtain ⟨-, G, B₀, h⟩ := hpre
    rw [h.funcs]; exact hfi
  · obtain ⟨rfl, G, B₀, h⟩ := hpre
    rw [hmod, ← code_eq]
    have hsz := h.size₁
    exact stream_hwp (accX_mi top B₁) (callsOk (accX_mi top B₁) (accX_code top B₁))
      (accX_abi top (size_lt hsz)) (accStore_shape h) (by rw [hsz]; exact hpp)
      (by rw [hsz]; exact hcp)

set_option maxHeartbeats 1000000 in
/-- `check-nested` meets its specification. -/
theorem checkNested_spec {top : BitVec 32} {B₁ : ByteArray} {pp pl cp cl : BitVec 32}
    (hpp : NestedIn B₁ pp.toNat pl.toNat) (hcp : cp.toNat + 4 * cl.toNat ≤ memBytes) :
    FSpecValid P host 12 (checkSpec [Val.i32 pp, Val.i32 pl, Val.i32 cp, Val.i32 cl] top B₁
      (nestedAt B₁ pp.toNat pl.toNat ∈ UnsatNested)) := by
  obtain ⟨fi, f, ty, hfi, hf, hty, hcode, hmod, hexp⟩ := acc_fn 12 (by decide)
  rw [prog_f12] at hf
  cases hf
  cases (show ty = ty4c from Option.some.inj (hty.symm.trans rfl))
  refine FSpecValid.of_body_hwp (fun s _ hpre => ?_) hcode hexp
    (fun _ _ hpre => by rw [hpre.1]; rfl) fun s args hpre => ?_
  · obtain ⟨-, G, B₀, h⟩ := hpre
    rw [h.funcs]; exact hfi
  · obtain ⟨rfl, G, B₀, h⟩ := hpre
    rw [hmod, ← code_eq]
    have hsz := h.size₁
    exact nested_hwp (accX_mi top B₁) (callsOk (accX_mi top B₁) (accX_code top B₁))
      (accX_abi top (size_lt hsz)) (accStore_shape h) hpp (by rw [hsz]; exact hcp)

theorem checkPost_vals {Goal : Prop} {s : Store Nat} {r : BitVec 32}
    (h : checkPost (H := Nat) Goal s (.normal [Val.i32 r])) (hr : r ≠ 0#32) : Goal :=
  h r rfl hr

/-- **Soundness of `check-stream`.** -/
theorem checkStream_sound {s : Store Nat} {G : List (BitVec 32)} {B₀ B₁ : ByteArray}
    {top : BitVec 32} (hs : AccStore s G B₀ top B₁) {pp pl cp cl : BitVec 32}
    (hpp : pp.toNat + 4 * pl.toNat ≤ memBytes) (hcp : cp.toNat + 4 * cl.toNat ≤ memBytes)
    {s' : Store Nat} {f' : Frame} {r : BitVec 32}
    (hrun : Steps P host (invoke s 11 [Val.i32 pp, Val.i32 pl, Val.i32 cp, Val.i32 cl])
      ⟨s', f', vals [Val.i32 r]⟩) (hr : r ≠ 0#32) :
    wordsAt B₁ pp.toNat pl.toNat ∈ UnsatStream :=
  checkPost_vals (s := s') ((checkStream_spec (P := P) (host := host) hpp hcp).invoke_vals
    ⟨rfl, G, B₀, hs⟩ hrun) hr

/-- **Soundness of `check-nested`.** -/
theorem checkNested_sound {s : Store Nat} {G : List (BitVec 32)} {B₀ B₁ : ByteArray}
    {top : BitVec 32} (hs : AccStore s G B₀ top B₁) {pp pl cp cl : BitVec 32}
    (hpp : NestedIn B₁ pp.toNat pl.toNat) (hcp : cp.toNat + 4 * cl.toNat ≤ memBytes)
    {s' : Store Nat} {f' : Frame} {r : BitVec 32}
    (hrun : Steps P host (invoke s 12 [Val.i32 pp, Val.i32 pl, Val.i32 cp, Val.i32 cl])
      ⟨s', f', vals [Val.i32 r]⟩) (hr : r ≠ 0#32) :
    nestedAt B₁ pp.toNat pl.toNat ∈ UnsatNested :=
  checkPost_vals (s := s') ((checkNested_spec (P := P) (host := host) hpp hcp).invoke_vals
    ⟨rfl, G, B₀, hs⟩ hrun) hr

/-! ## `cabi_realloc` -/

/-- **`cabi_realloc`, every returning run** (the acceptor kit's `realloc_sound`): it answers one
value `r` and only sets the heap pointer, to `t'`, as `ReallocOk` says. -/
theorem realloc_sound {s : Store Nat} (hf : s.funcs = accS.funcs) {top : BitVec 32}
    (hg : s.globals[8]? = some ⟨accGt, Val.i32 top⟩) (htop : top.toNat ≤ memBytes)
    {old osz al nsz : BitVec 32} {s' : Store Nat} {f' : Frame} {res : List Val}
    (hrun : Steps P host (invoke s 10 [Val.i32 old, Val.i32 osz, Val.i32 al, Val.i32 nsz])
      ⟨s', f', vals res⟩) :
    ∃ r t' : BitVec 32, res = [Val.i32 r] ∧ s' = s.setGlobal 8 (Val.i32 t') ∧
      ReallocOk top al nsz r t' := by
  obtain ⟨fi, f, ty, hfi, hf₁₀, hty, hcode, hmod, hexp⟩ := acc_fn 10 (by decide)
  cases (show f = reallocFunc from Option.some.inj hf₁₀.symm)
  cases (show ty = ty4c from Option.some.inj (hty.symm.trans rfl))
  exact Silmaril.Wasm.Acceptor.realloc_sound (by decide) (by decide) (by rw [hf]; exact hfi) hcode
    hexp rfl rfl (by rw [hmod, acc_mi.1]; rfl) hg htop hrun

end Silmaril.Proofs.Wasm.Examples.LratAccept
