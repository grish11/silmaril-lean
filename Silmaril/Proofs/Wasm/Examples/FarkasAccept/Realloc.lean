module

public import Silmaril.Proofs.Wasm.Examples.FarkasAccept.Abi

@[expose] public section

/-!
# `cabi_realloc`, every run

`realloc_hwp`: in any store whose global `4` (through the module instance) is the `i32` heap
pointer `top ≤ memBytes`, every run of the body of `cabi_realloc(old, osz, al, nsz)` returns one
value `r` and only sets global `4`, to some `t'`, with `top ≤ t' ≤ memBytes`, and either the
allocation succeeded (`r = align_up(top, al)`, `top ≤ r`, `r + nsz = t'`) or it failed
(`r = t' = memBytes`). So blocks returned within memory never overlap each other or anything
below the heap pointer. It never traps. Every profile and host relation.

A Silmaril addition.
-/

namespace Silmaril.Proofs.Wasm.Examples.FarkasAccept

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Examples.LRAT Silmaril.Wasm.Examples.Common
open Silmaril.Wasm.Examples.FarkasAccept (reallocBody gHeap memBytes alignUp ReallocOk)

variable {H : Type} {P : Profile} {host : HostSemantics H}
variable {s : Store H} {mi : ModuleInst} {L : List (BitVec 32)} {rs : List Val} {rest : List Admin}
  {Q : Post H} {gt : CGlobalType} {top : BitVec 32} {g : GlobalInst}

theorem global?_4 (hmi : mi.globals[4]? = some 4) (hs : s.globals[4]? = some g) :
    s.global? (fr mi L) ⟨⟨4 % 2 ^ 32, Nat.mod_lt _ (by decide)⟩⟩ = some (4, g) := by
  simp [Store.global?, fr, Idx.toNat, hmi, hs]

/-- `global.get 4`. -/
theorem w_ggetH (hmi : mi.globals[4]? = some 4) (hs : s.globals[4]? = some g)
    (h : HWP P host s (fr mi L) (vals (g.value :: rs).reverse ++ rest) Q) :
    HWP P host s (fr mi L) (vals rs.reverse ++ .plain (gget gHeap) :: rest) Q := by
  rw [vals_rev_cons, List.append_assoc] at h
  exact Wp.globalGet (m := .part) (global?_4 hmi hs) (by simpa using h)

/-- `global.get 4` of an `i32` global. -/
theorem w_ggetHv {v : BitVec 32} (hmi : mi.globals[4]? = some 4)
    (hs : s.globals[4]? = some ⟨gt, Val.i32 v⟩)
    (h : HWP P host s (fr mi L) (vals (Val.i32 v :: rs).reverse ++ rest) Q) :
    HWP P host s (fr mi L) (vals rs.reverse ++ .plain (gget gHeap) :: rest) Q :=
  w_ggetH hmi hs h

/-- `global.set 4`. -/
theorem w_gsetH' (hmi : mi.globals[4]? = some 4) (hs : s.globals[4]? = some g)
    {v : BitVec 32} (h : HWP P host (s.setGlobal 4 (Val.i32 v)) (fr mi L) (vals rs.reverse ++ rest) Q) :
    HWP P host s (fr mi L) (vals (Val.i32 v :: rs).reverse ++ .plain (gset gHeap) :: rest) Q := by
  rw [vals_rev_cons, show vals rs.reverse ++ [(Val.i32 v).toAdmin] =
    vals (rs.reverse ++ [Val.i32 v]) by simp]
  exact Wp.globalSet (m := .part) (global?_4 hmi hs) h

/-- The postcondition of the body: one result and only the heap pointer changed. -/
def reallocPost (s : Store H) (top al nsz : BitVec 32) : Store H → Outcome → Prop :=
  fun s' o => ∃ r t' : BitVec 32, o = .normal [Val.i32 r] ∧ s' = s.setGlobal 4 (Val.i32 t') ∧
    ReallocOk top al nsz r t'

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
set_option linter.unusedTactic false in
/-- **`cabi_realloc`, every run.** -/
theorem realloc_hwp (hmi : mi.globals[4]? = some 4)
    (hs : s.globals[4]? = some ⟨gt, Val.i32 top⟩) (htop : top.toNat ≤ memBytes)
    (old osz al nsz : BitVec 32) :
    HWP P host s (fr mi [old, osz, al, nsz, 0, 0])
      (vals ([] : List Val).reverse ++ expression reallocBody ++ [])
      (bodyPost 1 (reallocPost s top al nsz)) := by
  simp only [reallocBody, expression, List.map_cons, List.map_nil, List.cons_append,
    List.append_assoc]
  refine w_ggetHv hmi hs ?_
  repeat (wstep; fnorm)
  refine w_ggetHv hmi hs ?_
  repeat (wstep; fnorm)
  rw [b32_and, b32_and]
  generalize hp : (top + (al - BitVec.ofNat 32 1)) &&& (BitVec.ofNat 32 0 - al) = p
  have hpa : p = alignUp top al := by rw [← hp]; rfl
  by_cases hfit : (top.toNat ≤ p.toNat ∧ p.toNat ≤ (BitVec.ofNat 32 memBytes).toNat) ∧
      nsz.toNat ≤ (BitVec.ofNat 32 memBytes - p).toNat
  · refine w_if (fun _ => ?_) (fun hc => absurd hfit (b32_eq_zero.1 hc))
    simp only [expression, List.map_cons, List.map_nil]
    wstep; fnorm
    wstep; fnorm
    wstep
    refine w_gsetH' hmi hs ?_
    refine w_armEnd ?_
    wstep; fnorm
    wstep
    refine w_if (fun hc => absurd hfit (b32_eq_zero.1 (b32_ne_zero.1 hc))) (fun _ => ?_)
    wstep; fnorm
    refine w_end ⟨rfl, p, p + nsz, rfl, rfl, ?_⟩
    simp only [ReallocOk, memBytes, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hfit htop ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hfit
    have h3' : nsz.toNat ≤ 1048576 - p.toNat := by
      have : (BitVec.ofNat 32 1048576 - p).toNat = 1048576 - p.toNat := by bv_omega
      omega
    have hsum : (p + nsz).toNat = p.toNat + nsz.toNat := by bv_omega
    refine ⟨by omega, by omega, .inl ⟨hpa, h1, hsum.symm⟩⟩
  · refine w_if (fun hc => absurd (b32_ne_zero.1 hc) hfit) (fun _ => ?_)
    wstep; fnorm
    wstep
    refine w_if (fun _ => ?_) (fun hc => absurd (b32_eq_zero.2 hfit) (b32_eq_zero.1 hc))
    simp only [expression, List.map_cons, List.map_nil]
    wstep
    refine w_gsetH' hmi hs ?_
    wstep
    refine w_lset (by simp) (by decide) ?_
    fnorm
    refine w_armEnd ?_
    wstep; fnorm
    refine w_end ⟨rfl, BitVec.ofNat 32 memBytes, BitVec.ofNat 32 memBytes, rfl, rfl, ?_⟩
    simp only [ReallocOk, memBytes, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at htop ⊢
    refine ⟨htop, ?_, Or.inr ⟨?_, ?_⟩⟩ <;> simp

end Silmaril.Proofs.Wasm.Examples.FarkasAccept
