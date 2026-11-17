module

public import Silmaril.Proofs.Wasm.Examples.LratAccept.Component.Inst
public import Silmaril.Wasm.Component.Reference.ListLift.Thms
public import Silmaril.Wasm.Component.Reference.ListLift.Bump.Thms

/-!
# The LRAT acceptor component: soundness of accepting calls

An accepting call of `check-stream` (resp. `check-nested`) has, by `acceptSound lratComp`, a
Core-level explanation: the lowering `LParams` of the two lists into memory address `1` from the
instance store to a store `s`, and a run of the core function from `s` returning a nonzero `i32`.
The lowering ends in a store of the acceptor (`AccStore`, `params_holds` with the bump allocator
`lratBump`) with the arguments in its ABI memory (read back by `holdsL_words` and
`holdsL_nested`), so the core soundness theorems (`Silmaril.Wasm.Examples.LratAccept.checkStream_sound`,
`checkNested_sound`) put the problem in `UnsatStream` (resp. `UnsatNested`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Examples.LratAccept.Component

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Examples.LratAccept
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.ListLift
open Silmaril.Wasm.Logic.Words (wd words)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Logic.SAT.Carrier (UnsatStream UnsatNested)

/-! ## Reading the nested input -/

theorem nestedAt_succ (B : ByteArray) (q n : Nat) :
    nestedAt B q (n + 1) = words B (wd B q).toNat (wd B (q + 4)).toNat :: nestedAt B (q + 8) n := by
  unfold nestedAt
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, Nat.succ_eq_add_one]
  rw [show q + 8 * (i + 1) = q + 8 + 8 * i by omega]

/-- **The clauses of a `list<list<s32>>` are the words of their blocks.** -/
theorem holdsL_nested {B : ByteArray} {lo hi : Nat} :
    ∀ (p : List (List (BitVec 32))) (q : Nat),
      HoldsL B lo hi (.list .s32) (p.map LVal.ofWords) q →
      nestedAt B q p.length = p ∧
        ∀ i < p.length, (wd B (q + 8 * i)).toNat + 4 * (wd B (q + 8 * i + 4)).toNat ≤ B.size
  | [], _, _ => ⟨rfl, by simp⟩
  | c :: p, q, h => by
    simp only [List.map_cons, HoldsL, LVal.ofWords, Holds, LTy.size_s32, LTy.size_list,
      List.length_map] at h
    obtain ⟨⟨_, hlen, -, -, hb, hc⟩, hrest⟩ := h
    obtain ⟨ih1, ih2⟩ := holdsL_nested p (q + 8) hrest
    refine ⟨?_, ?_⟩
    · rw [List.length_cons, nestedAt_succ, ih1, hlen, holdsL_words c _ hc]
    · intro i hi
      cases i with
      | zero =>
        simp only [Nat.mul_zero, Nat.add_zero]
        rw [hlen]
        omega
      | succ i =>
        have := ih2 i (by simp only [List.length_cons] at hi; omega)
        rw [show q + 8 * (i + 1) = q + 8 + 8 * i by omega]
        exact this

/-! ## The lowering of the two arguments -/

/-- **The two lowered arguments in memory**: a list of type `list<t>` and the certificate words,
lowered into memory address `1`, end in a store of the acceptor whose ABI memory holds them. -/
theorem lower2 {P : Profile} {t : LTy} {us : List LVal} {cs : List (BitVec 32)} {s : Store Nat}
    {fl : List Core.Val}
    (hL : LParams P 10 1 [.list t, .list .s32] [.list us, LVal.ofWords cs] accI.store fl s) :
    ∃ q₁ q₂ G B₀ top B₁ lo hi, fl = [.i32 (BitVec.ofNat 32 q₁),
        .i32 (BitVec.ofNat 32 us.length), .i32 (BitVec.ofNat 32 q₂),
        .i32 (BitVec.ofNat 32 cs.length)] ∧
      q₁ < 2 ^ 32 ∧ q₂ < 2 ^ 32 ∧ us.length < 2 ^ 32 ∧ cs.length < 2 ^ 32 ∧
      AccStore s G B₀ top B₁ ∧
      q₁ + us.length * t.size ≤ B₁.size ∧ HoldsL B₁ lo hi t us q₁ ∧
      q₂ + 4 * cs.length ≤ B₁.size ∧ words B₁ q₂ cs.length = cs := by
  obtain ⟨t₁, ⟨⟨G, B₀, B₁, hs⟩, -⟩, -, -, hF⟩ := params_holds (lratBump P) hL lInvL_init
  have hBm : memBytesOf s 1 = B₁ := by simp [memBytesOf, hs.mems]
  rw [hBm] at hF
  simp only [FlatHolds, LVal.ofWords, List.length_map, LTy.size_s32] at hF
  obtain ⟨q₁, fl₁, rfl, hq₁, hl₁, -, -, hb₁, hL₁, q₂, fl₂, rfl, hq₂, hl₂, -, -, hb₂, hL₂, rfl⟩ := hF
  refine ⟨q₁, q₂, G, B₀, _, B₁, heapBase, t₁, rfl, hq₁, hq₂, hl₁, hl₂, hs, hb₁, hL₁, by omega, ?_⟩
  have := holdsL_words cs q₂ hL₂
  simpa using this

theorem checkList_s32 : ∀ xs : List (BitVec 32), LTy.checkList .s32 (xs.map .s32) = true
  | [] => rfl
  | x :: xs => by simp [LTy.checkList, LTy.check, checkList_s32 xs]

theorem checkList_nested : ∀ p : List (List (BitVec 32)),
    LTy.checkList (.list .s32) (p.map LVal.ofWords) = true
  | [] => rfl
  | c :: p => by
    simp [LTy.checkList, LTy.check, LVal.ofWords, checkList_s32, checkList_nested p]

/-! ## The headline results -/

/-- **An accepting call of `check-stream` is on an unsatisfiable stream.** -/
theorem checkStream_sound (P : Profile) (prof : ProfileKind) (xs cs : List (BitVec 32))
    (h : Outcome.returns (some [.bool true]) ∈ exportBehaviours prof (refHost P) () lratComp.toRef
      [] "check-stream" [(LVal.ofWords xs).toRef, (LVal.ofWords cs).toRef]) :
    xs ∈ UnsatStream := by
  have hx : (⟨"check-stream", [("problem", .list .s32), ("cert", .list .s32)], "check-stream"⟩ :
      ListExport) ∈ lratComp.exports := List.mem_cons_self
  have hc : LTy.checkParams [.list .s32, .list .s32] [LVal.ofWords xs, LVal.ofWords cs] = true := by
    simp [LTy.checkParams, LVal.ofWords, LTy.check, checkList_s32]
  obtain ⟨s, fl, s', f', r, hL, hS, hr⟩ :=
    acceptSound lratComp P prof accI lratComp_good lratComp_inst _ hx _ hc h
  change LParams P (lratComp.coreAddr accI "cabi_realloc") 1 [.list .s32, .list .s32] _ accI.store
    fl s at hL
  change Steps _ _ (invoke s (lratComp.coreAddr accI "check-stream") fl) _ at hS
  rw [t_coreAddrs.1] at hL
  rw [t_coreAddrs.2.1] at hS
  obtain ⟨q₁, q₂, G, B₀, top, B₁, lo, hi, rfl, hq₁, hq₂, hl₁, hl₂, hs, hb₁, hL₁, hb₂, hw₂⟩ :=
    lower2 (us := xs.map LVal.s32) hL
  simp only [List.length_map, LTy.size_s32] at hb₁ hL₁ hl₁ hS
  have hw₁ := holdsL_words xs q₁ hL₁
  have hB := hs.size₁
  have hU := Silmaril.Wasm.Examples.LratAccept.checkStream_sound (pp := BitVec.ofNat 32 q₁)
    (pl := BitVec.ofNat 32 xs.length) (cp := BitVec.ofNat 32 q₂) (cl := BitVec.ofNat 32 cs.length)
    hs (by rw [toNat_ofNat hq₁, toNat_ofNat hl₁]; omega)
    (by rw [toNat_ofNat hq₂, toNat_ofNat hl₂]; omega) hS hr
  rw [toNat_ofNat hq₁, toNat_ofNat hl₁] at hU
  simpa only [wordsAt, hw₁] using hU

/-- **An accepting call of `check-nested` is on an unsatisfiable formula.** -/
theorem checkNested_sound (P : Profile) (prof : ProfileKind) (p : List (List (BitVec 32)))
    (cs : List (BitVec 32))
    (h : Outcome.returns (some [.bool true]) ∈ exportBehaviours prof (refHost P) () lratComp.toRef
      [] "check-nested" [(LVal.ofNested p).toRef, (LVal.ofWords cs).toRef]) :
    p ∈ UnsatNested := by
  have hx : (⟨"check-nested", [("problem", .list (.list .s32)), ("cert", .list .s32)],
      "check-nested"⟩ : ListExport) ∈ lratComp.exports := List.mem_cons_of_mem _ List.mem_cons_self
  have hc : LTy.checkParams [.list (.list .s32), .list .s32] [LVal.ofNested p, LVal.ofWords cs] =
      true := by
    simp [LTy.checkParams, LVal.ofNested, LVal.ofWords, LTy.check, checkList_s32,
      checkList_nested]
  obtain ⟨s, fl, s', f', r, hL, hS, hr⟩ :=
    acceptSound lratComp P prof accI lratComp_good lratComp_inst _ hx _ hc h
  change LParams P (lratComp.coreAddr accI "cabi_realloc") 1 [.list (.list .s32), .list .s32] _
    accI.store fl s at hL
  change Steps _ _ (invoke s (lratComp.coreAddr accI "check-nested") fl) _ at hS
  rw [t_coreAddrs.1] at hL
  rw [t_coreAddrs.2.2] at hS
  obtain ⟨q₁, q₂, G, B₀, top, B₁, lo, hi, rfl, hq₁, hq₂, hl₁, hl₂, hs, hb₁, hL₁, hb₂, hw₂⟩ :=
    lower2 (us := p.map LVal.ofWords) hL
  simp only [List.length_map, LTy.size_list] at hb₁ hL₁ hl₁ hS
  obtain ⟨hn₁, hin⟩ := holdsL_nested p q₁ hL₁
  have hB := hs.size₁
  have hU := Silmaril.Wasm.Examples.LratAccept.checkNested_sound (pp := BitVec.ofNat 32 q₁)
    (pl := BitVec.ofNat 32 p.length) (cp := BitVec.ofNat 32 q₂) (cl := BitVec.ofNat 32 cs.length)
    hs (by rw [toNat_ofNat hq₁, toNat_ofNat hl₁]; exact ⟨by omega, hin⟩)
    (by rw [toNat_ofNat hq₂, toNat_ofNat hl₂]; omega) hS hr
  rw [toNat_ofNat hq₁, toNat_ofNat hl₁, hn₁] at hU
  exact hU

end Silmaril.Proofs.Wasm.Examples.LratAccept.Component
