module

public import Silmaril.Proofs.Wasm.Examples.FarkasAccept.Inst
public import Silmaril.Wasm.Acceptor.Code.Thms

@[expose] public section

/-!
# The checker's functions inside the acceptor: call specifications and call rules

`farkasMod`'s bodies are proved over the fixture view `withMachX X s m`
(`Silmaril.Wasm.Examples.Farkas.Fix`), which allows further globals and memories after the
checker's. In the acceptor's fixture `accX top B₁` the three checker functions get **function
specifications**, relative to `RepA top B₁ rs s` (the store holds a checker state with the
invariant `Inv` for the weighted rows `rs`):

* `row(y, b)` (function `0`) reaches `RepA ((Cmd.row y.toInt b.toInt).apply rs)`;
* `entry(j, a)` (function `1`) reaches `RepA ((Cmd.entry j.toNat a.toInt).apply rs)`;
* `check()` (function `2`), from **any** checker state with a one-page memory (`SizedA`),
  answers `v` and reaches `RepA []`, and `v ≠ 0` only if every `rs` the store represents is a
  valid certificate (`WRows.IsCert`).

The **call rules** `w_row`, `w_entry`, `w_check` use them for `call j` in the symbolic execution
of the acceptor's `check` (the acceptor kit's `w_callVoid`, `w_callI32`). Every profile and host relation. A Silmaril addition.
-/

namespace Silmaril.Proofs.Wasm.Examples.FarkasAccept

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Examples.Farkas
open Silmaril.Wasm.Examples.LRAT (fr vals_rev_cons vals_rev_cons₂)
open Silmaril.Wasm.Examples.Common (bodyPost FSpecValid.of_body_hwp)
open Silmaril.Wasm.Examples.FarkasAccept (callf accS)
open Silmaril.Logic.LinArith (WRows Cmd)
open Silmaril.Wasm.Acceptor (w_callVoid w_callI32)

variable {P : Profile} {host : HostSemantics Nat} {top : BitVec 32} {B₁ : ByteArray}

/-! ## The representation -/

/-- The store holds a checker state, in the acceptor's fixture, with the invariant for `rs`. -/
def RepA (top : BitVec 32) (B₁ : ByteArray) (rs : WRows) (s : Store Nat) : Prop :=
  ∃ m, HoldsX (accX top B₁) accS.funcs s m ∧ Inv m rs

/-- The store holds a checker state, in the acceptor's fixture, with a one-page memory. -/
def SizedA (top : BitVec 32) (B₁ : ByteArray) (s : Store Nat) : Prop :=
  ∃ m, HoldsX (accX top B₁) accS.funcs s m ∧ m.mem.size = 65536

theorem RepA.funcs {rs : WRows} {s : Store Nat} (h : RepA top B₁ rs s) : s.funcs = accS.funcs := by
  obtain ⟨m, ⟨s₀, hs₀, rfl⟩, -⟩ := h
  exact hs₀

theorem SizedA.funcs {s : Store Nat} (h : SizedA top B₁ s) : s.funcs = accS.funcs := by
  obtain ⟨m, ⟨s₀, hs₀, rfl⟩, -⟩ := h
  exact hs₀

theorem RepA.sized {rs : WRows} {s : Store Nat} (h : RepA top B₁ rs s) : SizedA top B₁ s := by
  obtain ⟨m, hH, hI⟩ := h
  exact ⟨m, hH, hI.1⟩

/-- The invariant of the state a store holds. -/
theorem repA_inv {s₀ : Store Nat} {m : Mach} (hs₀ : s₀.funcs = accS.funcs) {rs : WRows}
    (h : RepA top B₁ rs (withMachX (accX top B₁) s₀ m)) : Inv m rs := by
  obtain ⟨m', hH, hI⟩ := h
  have he : m' = m := HoldsX.unique hH (holdsX_withMachX hs₀ m)
  exact he ▸ hI

/-- A nonzero answer of `check` is `1`. -/
theorem checkRes_ne_zero {m : Mach} {nz : BitVec 32} (h : checkRes m nz ≠ 0) : checkRes m nz = 1 := by
  have hlt : ltS m.vb 0 = bool32 (decide (m.vb.toInt < 0)) := ltS_ofInt (by norm_num) (by norm_num)
  have he : checkRes m nz = bool32 ((m.bad == 0) && (nz == 0) && decide (m.vb.toInt < 0)) := by
    rw [checkRes, hlt]
    exact (congrArg (· &&& _) (bool32_and _ _)).trans (bool32_and _ _)
  rw [he] at h ⊢
  generalize ((m.bad == 0) && (nz == 0) && decide (m.vb.toInt < 0)) = b at h ⊢
  cases b
  · exact absurd rfl h
  · rfl

/-! ## Specifications -/

/-- `row(y, b)`. -/
def rowSpec (top : BitVec 32) (B₁ : ByteArray) (y b : BitVec 64) : FSpec Nat where
  pre s args := args = [Val.i64 y, Val.i64 b] ∧ ∃ rs, RepA top B₁ rs s
  post s _ s' o := o = .normal [] ∧
    ∀ rs, RepA top B₁ rs s → RepA top B₁ ((Cmd.row y.toInt b.toInt).apply rs) s'

/-- `entry(j, a)`. -/
def entrySpec (top : BitVec 32) (B₁ : ByteArray) (j : BitVec 32) (a : BitVec 64) : FSpec Nat where
  pre s args := args = [Val.i32 j, Val.i64 a] ∧ ∃ rs, RepA top B₁ rs s
  post s _ s' o := o = .normal [] ∧
    ∀ rs, RepA top B₁ rs s → RepA top B₁ ((Cmd.entry j.toNat a.toInt).apply rs) s'

/-- `check()`, from any checker state. -/
def checkSpec (top : BitVec 32) (B₁ : ByteArray) : FSpec Nat where
  pre s args := args = [] ∧ SizedA top B₁ s
  post s _ s' o := ∃ v : BitVec 32, o = .normal [Val.i32 v] ∧ RepA top B₁ [] s' ∧
    ∀ rs, RepA top B₁ rs s → v ≠ 0#32 → WRows.IsCert rs

theorem prog_f0 : Silmaril.Wasm.Examples.FarkasAccept.prog.funcs[0]? =
    some ⟨⟨0⟩, [.i64], rowBody⟩ := rfl
theorem prog_f1 : Silmaril.Wasm.Examples.FarkasAccept.prog.funcs[1]? =
    some ⟨⟨1⟩, [.i32, .i64], entryBody⟩ := rfl
theorem prog_f2 : Silmaril.Wasm.Examples.FarkasAccept.prog.funcs[2]? =
    some ⟨⟨2⟩, [.i32, .i32], checkBody⟩ := rfl

theorem row_spec (y b : BitVec 64) : FSpecValid P host 0 (rowSpec top B₁ y b) := by
  obtain ⟨fi, f, ty, hfi, hf, hty, hcode, hmod, hexp⟩ := acc_fn 0 (by decide)
  rw [prog_f0] at hf
  cases hf
  cases (show ty = farkasTys[0] from Option.some.inj (hty.symm.trans rfl))
  refine FSpecValid.of_body_hwp (fun s _ hpre => ?_) hcode hexp
    (fun _ _ hpre => by rw [hpre.1]; rfl) fun s args hpre => ?_
  · obtain ⟨-, rs, h⟩ := hpre
    rw [h.funcs]; exact hfi
  · obtain ⟨rfl, rs, m, ⟨s₀, hs₀, rfl⟩, hI⟩ := hpre
    rw [hmod]
    refine row_hwpX (accX_ok top B₁) y b fun f' => ⟨rfl, rfl, fun rs' h' => ?_⟩
    exact ⟨rowM m y b, holdsX_withMachX hs₀ _, inv_row (repA_inv hs₀ h') y b⟩

theorem entry_spec (j : BitVec 32) (a : BitVec 64) : FSpecValid P host 1 (entrySpec top B₁ j a) := by
  obtain ⟨fi, f, ty, hfi, hf, hty, hcode, hmod, hexp⟩ := acc_fn 1 (by decide)
  rw [prog_f1] at hf
  cases hf
  cases (show ty = farkasTys[1] from Option.some.inj (hty.symm.trans rfl))
  refine FSpecValid.of_body_hwp (fun s _ hpre => ?_) hcode hexp
    (fun _ _ hpre => by rw [hpre.1]; rfl) fun s args hpre => ?_
  · obtain ⟨-, rs, h⟩ := hpre
    rw [h.funcs]; exact hfi
  · obtain ⟨rfl, rs, m, ⟨s₀, hs₀, rfl⟩, hI⟩ := hpre
    rw [hmod]
    refine entry_hwpX (accX_ok top B₁) hI.1 j a fun f' => ⟨rfl, rfl, fun rs' h' => ?_⟩
    exact ⟨entryM m j a, holdsX_withMachX hs₀ _, inv_entry (repA_inv hs₀ h') j a⟩

theorem check_spec : FSpecValid P host 2 (checkSpec top B₁) := by
  obtain ⟨fi, f, ty, hfi, hf, hty, hcode, hmod, hexp⟩ := acc_fn 2 (by decide)
  rw [prog_f2] at hf
  cases hf
  cases (show ty = farkasTys[2] from Option.some.inj (hty.symm.trans rfl))
  refine FSpecValid.of_body_hwp (fun s _ hpre => ?_) hcode hexp
    (fun _ _ hpre => by rw [hpre.1]; rfl) fun s args hpre => ?_
  · obtain ⟨-, h⟩ := hpre
    rw [h.funcs]; exact hfi
  · obtain ⟨rfl, m, ⟨s₀, hs₀, rfl⟩, hB⟩ := hpre
    rw [hmod]
    refine check_hwpX (accX_ok top B₁) hB fun B nz f' hd =>
      ⟨rfl, checkRes m nz, rfl, ⟨checkEnd B, holdsX_withMachX hs₀ _, inv_check hd⟩,
        fun rs h' hv => ?_⟩
    exact cert_of_check (repA_inv hs₀ h') hd (checkRes_ne_zero hv)

/-! ## Call rules -/

variable {s : Store Nat} {L : List (BitVec 32)} {vs : List Val} {rest : List Admin}
  {Q : Post Nat} {rs : WRows}

theorem accMi_funcs {j : Nat} (hj : j < 5) : accMi.funcs[j]? = some j := by
  rw [acc_mi.2.2, List.getElem?_range hj]

theorem acc_fi {j : Nat} (hj : j < 5) {s : Store Nat} (h : s.funcs = accS.funcs) :
    ∃ fi, s.funcs[j]? = some fi := by
  obtain ⟨fi, -, -, hfi, -⟩ := acc_fn j hj
  exact ⟨fi, by rw [h]; exact hfi⟩

/-- `row(y, b)`. -/
theorem w_row (hR : RepA top B₁ rs s) {y b : BitVec 64}
    (k : ∀ s', RepA top B₁ ((Cmd.row y.toInt b.toInt).apply rs) s' →
      HWP P host s' (fr accMi L) (vals vs.reverse ++ rest) Q) :
    HWP P host s (fr accMi L) (vals (Val.i64 b :: Val.i64 y :: vs).reverse ++
      .plain (callf 0) :: rest) Q := by
  rw [vals_rev_cons₂]
  obtain ⟨fi, hf⟩ := acc_fi (j := 0) (by decide) hR.funcs
  exact w_callVoid (by decide) (accMi_funcs (by decide)) hf (row_spec y b) ⟨rfl, rs, hR⟩
    (fun _ _ h => ⟨h.1, h.2 rs hR⟩) k

/-- `entry(j, a)`. -/
theorem w_entry (hR : RepA top B₁ rs s) {j : BitVec 32} {a : BitVec 64}
    (k : ∀ s', RepA top B₁ ((Cmd.entry j.toNat a.toInt).apply rs) s' →
      HWP P host s' (fr accMi L) (vals vs.reverse ++ rest) Q) :
    HWP P host s (fr accMi L) (vals (Val.i64 a :: Val.i32 j :: vs).reverse ++
      .plain (callf 1) :: rest) Q := by
  rw [vals_rev_cons₂]
  obtain ⟨fi, hf⟩ := acc_fi (j := 1) (by decide) hR.funcs
  exact w_callVoid (by decide) (accMi_funcs (by decide)) hf (entry_spec j a) ⟨rfl, rs, hR⟩
    (fun _ _ h => ⟨h.1, h.2 rs hR⟩) k

/-- `check()`, from any checker state. -/
theorem w_check (hS : SizedA top B₁ s)
    (k : ∀ s' v, RepA top B₁ [] s' → (∀ rs, RepA top B₁ rs s → v ≠ 0#32 → WRows.IsCert rs) →
      HWP P host s' (fr accMi L) (vals (Val.i32 v :: vs).reverse ++ rest) Q) :
    HWP P host s (fr accMi L) (vals vs.reverse ++ .plain (callf 2) :: rest) Q := by
  obtain ⟨fi, hf⟩ := acc_fi (j := 2) (by decide) hS.funcs
  have := w_callI32 (P := P) (host := host) (f := fr accMi L) (vs₀ := vs.reverse) (args := [])
    (rest := rest) (Q := Q)
    (R := fun s' v => RepA top B₁ [] s' ∧ ∀ rs, RepA top B₁ rs s → v ≠ 0#32 → WRows.IsCert rs)
    (by decide) (accMi_funcs (by decide)) hf check_spec ⟨rfl, hS⟩
    (fun _ _ ⟨v, hv, hR, hc⟩ => ⟨v, hv, hR, hc⟩) fun s' v ⟨hR, hc⟩ => by
      simpa using k s' v hR hc
  simpa using this

end Silmaril.Proofs.Wasm.Examples.FarkasAccept
