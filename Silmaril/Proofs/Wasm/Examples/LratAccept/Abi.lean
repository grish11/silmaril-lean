module

public import Silmaril.Proofs.Wasm.Examples.LratAccept.Dispatch

@[expose] public section

/-!
# The canonical-ABI memory and the heap pointer: rules

In the acceptor's fixture the LRAT view (`Shape X s G B`) is followed by one further memory, the
canonical-ABI memory holding the bytes `B₁` (memory `1` of the module instance), and one
further global, the heap pointer (global `8`). `Abi X B₁` records this; `w_load1` loads a word
of `B₁` and `w_gset8` writes the heap pointer (after which the acceptor's code no longer needs
the view). A Silmaril addition.
-/

namespace Silmaril.Proofs.Wasm.Examples.LratAccept

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Examples.LRAT
open Silmaril.Wasm.Examples.LratAccept

variable {H : Type} {P : Profile} {host : HostSemantics H} {X : Fix H}

/-- The fixture's further memory is the ABI memory `B₁` at index `1`, its further global the
heap pointer at index `8`. -/
structure Abi (X : Fix H) (B₁ : ByteArray) : Prop where
  mem1 : X.mi.mems[1]? = some 1
  mrest : ∃ mt, X.mrest[0]? = some ⟨mt, B₁⟩
  glob8 : X.mi.globals[8]? = some 8
  grest : ∃ g, X.grest[0]? = some g
  size : B₁.size < 2 ^ 32

variable {s : Store H} {G : List (BitVec 32)} {B B₁ : ByteArray} {L : List (BitVec 32)}
  {rs : List Val} {rest : List Admin} {Q : Post H}

/-- `i32.load` from the ABI memory, in bounds. -/
theorem w_load1 (hS : Shape X s G B) (hA : Abi X B₁) {a : BitVec 32} (hb : a.toNat + 4 ≤ B₁.size)
    (h : HWP P host s (fr X.mi L)
      (vals (Val.i32 (Silmaril.Wasm.Logic.Words.wd B₁ a.toNat) :: rs).reverse ++ rest) Q) :
    HWP P host s (fr X.mi L) (vals (Val.i32 a :: rs).reverse ++ .plain ld1 :: rest) Q := by
  obtain ⟨mt, hm⟩ := hA.mrest
  rw [vals_rev_push]
  rw [vals_rev_push] at h
  have hmem : s.mem? (fr X.mi L) ⟨1⟩ = some (1, ⟨mt, B₁⟩) := by
    simp [Store.mem?, fr, Idx.toNat, hA.mem1, hS.mem, hm]
  have hl : Memory.load B₁ (effAddr a.toNat ⟨2, 0⟩) (IntType.i32.width / 8) =
      some (Silmaril.Wasm.Logic.Words.wd B₁ a.toNat) :=
    load_wd (B := B₁) (by simp only [effAddr]; exact hb)
  exact Wp.intLoad (m := .part) (a := .i32) (i := a) hmem hl h

/-- `global.set 8` (the heap pointer). -/
theorem w_gset8 (hS : Shape X s G B) (hA : Abi X B₁) {v : BitVec 32}
    (h : ∀ s', HWP P host s' (fr X.mi L) (vals rs.reverse ++ rest) Q) :
    HWP P host s (fr X.mi L) (vals (Val.i32 v :: rs).reverse ++ .plain (gset 8) :: rest) Q := by
  obtain ⟨g, hg⟩ := hA.grest
  rw [vals_rev_cons, show vals rs.reverse ++ [(Val.i32 v).toAdmin] =
    vals (rs.reverse ++ [Val.i32 v]) by simp]
  have hk : (G.map fun v => (⟨X.gt, Val.i32 v⟩ : GlobalInst)).length = 8 := by simp [hS.len]
  have hglob : s.global? (fr X.mi L) ⟨⟨8 % 2 ^ 32, Nat.mod_lt _ (by decide)⟩⟩ = some (8, g) := by
    simp only [Store.global?, fr, Idx.toNat, hS.glob]
    simp [hA.glob8, List.getElem?_append_right (Nat.le_of_eq hk), hk, hg]
  exact Wp.globalSet (m := .part) hglob (h _)

theorem getD_set_ne {L : List (BitVec 32)} {k i : Nat} (h : k ≠ i) (v : BitVec 32) :
    (L.set k v).getD i 0 = L.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_set_self {L : List (BitVec 32)} {k : Nat} (h : k < L.length) (v : BitVec 32) :
    (L.set k v).getD k 0 = v := by
  simp [List.getD_eq_getElem?_getD, h]

end Silmaril.Proofs.Wasm.Examples.LratAccept
