module

public import Silmaril.Proofs.Wasm.Examples.FarkasAccept.Check
public import Silmaril.Proofs.Wasm.Examples.FarkasAccept.Realloc

@[expose] public section

/-!
# The acceptor's exports: every returning run

Function specifications of the two exported functions of the instantiated acceptor, from the
body proofs (`FSpecValid.of_body_hwp`), and their reading for every run of `$invoke`
(`FSpecValid.invoke_vals`):

* `check_sound`: in every store of the acceptor (`AccStore`: the instance's functions, any
  checker state, any heap pointer and a 1 MiB ABI memory `B₁`) holding the arguments in bounds,
  a run of `check` returning `[r]` with `r ≠ 0` puts the system read from `B₁` in `Infeasible`;
* `realloc_sound`: a returning run of `cabi_realloc` only sets the heap pointer, as `ReallocOk`
  says.

Every profile and host relation. A Silmaril addition.
-/

namespace Silmaril.Proofs.Wasm.Examples.FarkasAccept

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Examples.Common
open Silmaril.Wasm.Examples.FarkasAccept (prog accS AccStore systemAt IneqsIn memBytes accG32
  checkLocals checkBody reallocBody ReallocOk)
open Silmaril.Logic.LinArith.Carrier (Infeasible)

variable {P : Profile} {host : HostSemantics Nat}

/-- The specification of `check`: the arguments, a store of the acceptor; a nonzero answer
means `Goal`. -/
def acceptSpec (args₀ : List Val) (top : BitVec 32) (B₁ : ByteArray) (Goal : Prop) : FSpec Nat where
  pre s args := args = args₀ ∧ AccStore s top B₁
  post _ _ s' o := checkPost Goal s' o

theorem prog_f4 : prog.funcs[4]? = some ⟨⟨3⟩, checkLocals, checkBody⟩ := rfl
theorem prog_f3 : prog.funcs[3]? = some ⟨⟨3⟩, [.i32, .i32], reallocBody⟩ := rfl

set_option maxHeartbeats 1000000 in
/-- `check` meets its specification. -/
theorem accept_spec {top : BitVec 32} {B₁ : ByteArray} {sp sl yp yl : BitVec 32}
    (hsp : IneqsIn B₁ sp.toNat sl.toNat) (hyp : yp.toNat + 8 * yl.toNat ≤ memBytes) :
    FSpecValid P host 4 (acceptSpec [Val.i32 sp, Val.i32 sl, Val.i32 yp, Val.i32 yl] top B₁
      (systemAt B₁ sp.toNat sl.toNat ∈ Infeasible)) := by
  obtain ⟨fi, f, ty, hfi, hf, hty, hcode, hmod, hexp⟩ := acc_fn 4 (by decide)
  rw [prog_f4] at hf
  cases hf
  cases (show ty = ty4c from Option.some.inj (hty.symm.trans rfl))
  refine FSpecValid.of_body_hwp (fun s _ hpre => ?_) hcode hexp
    (fun _ _ hpre => by rw [hpre.1]; rfl) fun s args hpre => ?_
  · obtain ⟨-, h⟩ := hpre
    rw [h.funcs]; exact hfi
  · obtain ⟨rfl, h⟩ := hpre
    rw [hmod, ← Silmaril.Wasm.Examples.LRAT.code_eq]
    exact check_hwp h hsp (by rw [h.size₁]; exact hyp)

/-- **Soundness of `check`.** -/
theorem check_sound {s : Store Nat} {top : BitVec 32} {B₁ : ByteArray} (hs : AccStore s top B₁)
    {sp sl yp yl : BitVec 32} (hsp : IneqsIn B₁ sp.toNat sl.toNat)
    (hyp : yp.toNat + 8 * yl.toNat ≤ memBytes)
    {s' : Store Nat} {f' : Frame} {r : BitVec 32}
    (hrun : Steps P host (invoke s 4 [Val.i32 sp, Val.i32 sl, Val.i32 yp, Val.i32 yl])
      ⟨s', f', vals [Val.i32 r]⟩) (hr : r ≠ 0#32) :
    systemAt B₁ sp.toNat sl.toNat ∈ Infeasible :=
  (accept_spec (P := P) (host := host) (top := top) hsp hyp).invoke_vals ⟨rfl, hs⟩ hrun r rfl hr

/-! ## `cabi_realloc` -/

/-- The specification of `cabi_realloc`. -/
def reallocSpec (old osz al nsz top : BitVec 32) : FSpec Nat where
  pre s args := args = [Val.i32 old, Val.i32 osz, Val.i32 al, Val.i32 nsz] ∧
    s.funcs = accS.funcs ∧ s.globals[4]? = some ⟨accG32, Val.i32 top⟩
  post s _ s' o := reallocPost s top al nsz s' o

set_option maxHeartbeats 1000000 in
theorem realloc_spec {old osz al nsz top : BitVec 32} (htop : top.toNat ≤ memBytes) :
    FSpecValid P host 3 (reallocSpec old osz al nsz top) := by
  obtain ⟨fi, f, ty, hfi, hf, hty, hcode, hmod, hexp⟩ := acc_fn 3 (by decide)
  rw [prog_f3] at hf
  cases hf
  cases (show ty = ty4c from Option.some.inj (hty.symm.trans rfl))
  refine FSpecValid.of_body_hwp (fun s _ hpre => ?_) hcode hexp
    (fun _ _ hpre => by rw [hpre.1]; rfl) fun s args hpre => ?_
  · obtain ⟨-, h, -⟩ := hpre
    rw [h]; exact hfi
  · obtain ⟨rfl, -, hg⟩ := hpre
    rw [hmod, ← Silmaril.Wasm.Examples.LRAT.code_eq]
    exact realloc_hwp (by rw [acc_mi.1]; rfl) hg htop old osz al nsz

/-- **`cabi_realloc`, every returning run**: it answers one value `r` and only sets the heap
pointer, to `t'`, as `ReallocOk` says. -/
theorem realloc_sound {s : Store Nat} (hf : s.funcs = accS.funcs) {top : BitVec 32}
    (hg : s.globals[4]? = some ⟨accG32, Val.i32 top⟩) (htop : top.toNat ≤ memBytes)
    {old osz al nsz : BitVec 32} {s' : Store Nat} {f' : Frame} {res : List Val}
    (hrun : Steps P host (invoke s 3 [Val.i32 old, Val.i32 osz, Val.i32 al, Val.i32 nsz])
      ⟨s', f', vals res⟩) :
    ∃ r t' : BitVec 32, res = [Val.i32 r] ∧ s' = s.setGlobal 4 (Val.i32 t') ∧
      ReallocOk top al nsz r t' := by
  obtain ⟨r, t', ho, hs', hok⟩ := (realloc_spec (P := P) (host := host) (old := old) (osz := osz)
    (al := al) (nsz := nsz) htop).invoke_vals ⟨rfl, hf, hg⟩ hrun
  cases ho
  exact ⟨r, t', rfl, hs', hok⟩

end Silmaril.Proofs.Wasm.Examples.FarkasAccept
