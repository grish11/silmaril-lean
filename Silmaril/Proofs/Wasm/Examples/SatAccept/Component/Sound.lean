module

public import Silmaril.Proofs.Wasm.Examples.SatAccept.Component.Inst
public import Silmaril.Wasm.Component.Reference.ListLift.Thms
public import Silmaril.Wasm.Component.Reference.ListLift.Bump.Thms
public import Silmaril.Logic.SAT.Carrier.Thms

/-!
# The SAT acceptor component: soundness of accepting calls

An accepting call of `check-stream` (resp. `check-nested`) has, by `acceptSound satComp`, a
Core-level explanation: the lowering `LParams` of the two lists from the instance store to a
store `s`, and a run of the core function from `s` returning a nonzero `i32`. The lowering ends
with the arguments in memory (`params_holds` with the bump allocator `satBump`, read back by
`holdsL_words` and `holdsL_nested`), so the core function's specification (`stream_returns`,
`nested_returns`) says that the answer is `satStream xs ms` (resp. `satNested p ms`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Examples.SatAccept.Component

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation Silmaril.Wasm.Game
open Silmaril.Wasm.Examples.SatAccept
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.ListLift
open Silmaril.Wasm.Logic.Words (wd words MemAt)
open Silmaril.Wasm.Logic.VC (globalVal)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Logic.SAT.Carrier (satStream satNested)

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

/-- **The two lowered arguments in memory**: a list of type `list<t>` and the model words. -/
theorem lower2 {P : Profile} {t : LTy} {us : List LVal} {ms : List (BitVec 32)} {s : Store Nat}
    {fl : List Core.Val}
    (hL : LParams P 0 0 [.list t, .list .s32] [.list us, LVal.ofWords ms] satI.store fl s) :
    ∃ q₁ q₂ mt B lo hi, fl = [.i32 (BitVec.ofNat 32 q₁), .i32 (BitVec.ofNat 32 us.length),
        .i32 (BitVec.ofNat 32 q₂), .i32 (BitVec.ofNat 32 ms.length)] ∧
      q₁ < 2 ^ 32 ∧ q₂ < 2 ^ 32 ∧ us.length < 2 ^ 32 ∧ ms.length < 2 ^ 32 ∧
      s.funcs = satI.store.funcs ∧ s.mems[0]? = some ⟨mt, B⟩ ∧ B.size = memBytes ∧
      (globalVal s satM 0).isSome ∧
      q₁ + us.length * t.size ≤ B.size ∧ HoldsL B lo hi t us q₁ ∧
      q₂ + 4 * ms.length ≤ B.size ∧ words B q₂ ms.length = ms := by
  obtain ⟨t₁, ⟨hf, ⟨mt, B, hm, hB⟩, hg, -⟩, -, -, hF⟩ := params_holds (satBump P) hL sInv_init
  have hBm : memBytesOf s 0 = B := by simp [memBytesOf, hm]
  rw [hBm] at hF
  simp only [FlatHolds, LVal.ofWords, List.length_map, LTy.size_s32] at hF
  obtain ⟨q₁, fl₁, rfl, hq₁, hl₁, -, -, hb₁, hL₁, q₂, fl₂, rfl, hq₂, hl₂, -, -, hb₂, hL₂, rfl⟩ := hF
  refine ⟨q₁, q₂, mt, B, heapBase, t₁, rfl, hq₁, hq₂, hl₁, hl₂, hf, hm, hB, by rw [hg]; rfl,
    hb₁, hL₁, by omega, ?_⟩
  have := holdsL_words ms q₂ hL₂
  simpa using this

theorem toNat_ofNat {q : Nat} (h : q < 2 ^ 32) : (BitVec.ofNat 32 q).toNat = q := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem checkList_s32 : ∀ xs : List (BitVec 32), LTy.checkList .s32 (xs.map .s32) = true
  | [] => rfl
  | x :: xs => by simp [LTy.checkList, LTy.check, checkList_s32 xs]

theorem checkList_nested : ∀ p : List (List (BitVec 32)),
    LTy.checkList (.list .s32) (p.map LVal.ofWords) = true
  | [] => rfl
  | c :: p => by
    simp [LTy.checkList, LTy.check, LVal.ofWords, checkList_s32, checkList_nested p]

/-! ## The headline results -/

/-- **An accepting call of `check-stream` answers `satStream`.** -/
theorem checkStream_sound (P : Profile) (prof : ProfileKind) (xs ms : List (BitVec 32))
    (h : Outcome.returns (some [.bool true]) ∈ exportBehaviours prof (refHost P) () satComp.toRef
      [] "check-stream" [(LVal.ofWords xs).toRef, (LVal.ofWords ms).toRef]) :
    satStream xs ms = true := by
  have hx : (⟨"check-stream", [("problem", .list .s32), ("model", .list .s32)], "check-stream"⟩ :
      ListExport) ∈ satComp.exports := List.mem_cons_self
  have hc : LTy.checkParams [.list .s32, .list .s32] [LVal.ofWords xs, LVal.ofWords ms] = true := by
    simp [LTy.checkParams, LVal.ofWords, LTy.check, checkList_s32]
  obtain ⟨s, fl, s', f', r, hL, hS, hr⟩ :=
    acceptSound satComp P prof satI satComp_good satComp_inst _ hx _ hc h
  change LParams P (satComp.coreAddr satI "cabi_realloc") 0 [.list .s32, .list .s32] _ satI.store
    fl s at hL
  change Steps _ _ (invoke s (satComp.coreAddr satI "check-stream") fl) _ at hS
  rw [t_coreAddrs.1] at hL
  rw [t_coreAddrs.2.1] at hS
  obtain ⟨q₁, q₂, mt, B, lo, hi, rfl, hq₁, hq₂, hl₁, hl₂, hf, hm, hB, hg, hb₁, hL₁, hb₂, hw₂⟩ :=
    lower2 (us := xs.map LVal.s32) hL
  obtain ⟨f₀, f₁, f₂, hF, -, hc₁, -, -, he₁, -, -, hm₁, -, hg₀, hg₁, -⟩ := funcs_eq
  have hfi : s.funcs[1]? = some f₁ := by rw [hf, hF]; rfl
  have hmem : MemAt s f₁.module 0 mt B := ⟨by rw [hm₁]; rfl, hm⟩
  have hg' : (globalVal s f₁.module 0).isSome := by
    rw [globalVal_congr (m' := satM) (by rw [satM_eq hF, hg₁, hg₀]) 0]
    exact hg
  simp only [List.length_map, LTy.size_s32] at hb₁ hL₁ hl₁ hS
  have hw₁ := holdsL_words xs q₁ hL₁
  obtain ⟨-, hres⟩ := stream_returns (pp := BitVec.ofNat 32 q₁) (pl := BitVec.ofNat 32 xs.length)
    (mp := BitVec.ofNat 32 q₂) (ml := BitVec.ofNat 32 ms.length) hfi hc₁ he₁ ty4_params
    ty4_results hmem hB (by rw [toNat_ofNat hq₁, toNat_ofNat hl₁]; omega)
    (by rw [toNat_ofNat hq₂, toNat_ofNat hl₂]; omega) hg' hS
  rw [toNat_ofNat hq₁, toNat_ofNat hl₁, toNat_ofNat hq₂, toNat_ofNat hl₂] at hres
  simp only [wordsAt, hw₁, hw₂, List.cons.injEq, and_true] at hres
  have hr' := i32_inj hres
  by_contra hn
  simp only [Bool.not_eq_true] at hn
  simp [hn] at hr'
  exact hr hr'

/-- **An accepting call of `check-nested` answers `satNested`.** -/
theorem checkNested_sound (P : Profile) (prof : ProfileKind) (p : List (List (BitVec 32))) (ms : List (BitVec 32))
    (h : Outcome.returns (some [.bool true]) ∈ exportBehaviours prof (refHost P) () satComp.toRef
      [] "check-nested" [(LVal.ofNested p).toRef, (LVal.ofWords ms).toRef]) :
    satNested p ms = true := by
  have hx : (⟨"check-nested", [("problem", .list (.list .s32)), ("model", .list .s32)],
      "check-nested"⟩ : ListExport) ∈ satComp.exports := List.mem_cons_of_mem _ List.mem_cons_self
  have hc : LTy.checkParams [.list (.list .s32), .list .s32] [LVal.ofNested p, LVal.ofWords ms] =
      true := by
    simp [LTy.checkParams, LVal.ofNested, LVal.ofWords, LTy.check, checkList_s32,
      checkList_nested]
  obtain ⟨s, fl, s', f', r, hL, hS, hr⟩ :=
    acceptSound satComp P prof satI satComp_good satComp_inst _ hx _ hc h
  change LParams P (satComp.coreAddr satI "cabi_realloc") 0 [.list (.list .s32), .list .s32] _ satI.store
    fl s at hL
  change Steps _ _ (invoke s (satComp.coreAddr satI "check-nested") fl) _ at hS
  rw [t_coreAddrs.1] at hL
  rw [t_coreAddrs.2.2] at hS
  obtain ⟨q₁, q₂, mt, B, lo, hi, rfl, hq₁, hq₂, hl₁, hl₂, hf, hm, hB, hg, hb₁, hL₁, hb₂, hw₂⟩ :=
    lower2 (us := p.map LVal.ofWords) hL
  obtain ⟨f₀, f₁, f₂, hF, -, -, hc₁, -, -, he₁, -, -, hm₁, hg₀, -, hg₁⟩ := funcs_eq
  have hfi : s.funcs[2]? = some f₂ := by rw [hf, hF]; rfl
  have hmem : MemAt s f₂.module 0 mt B := ⟨by rw [hm₁]; rfl, hm⟩
  have hg' : (globalVal s f₂.module 0).isSome := by
    rw [globalVal_congr (m' := satM) (by rw [satM_eq hF, hg₁, hg₀]) 0]
    exact hg
  simp only [List.length_map, LTy.size_list] at hb₁ hL₁ hl₁ hS
  obtain ⟨hn₁, hin⟩ := holdsL_nested p q₁ hL₁
  obtain ⟨-, hres⟩ := nested_returns (pp := BitVec.ofNat 32 q₁) (pl := BitVec.ofNat 32 p.length)
    (mp := BitVec.ofNat 32 q₂) (ml := BitVec.ofNat 32 ms.length) hfi hc₁ he₁ ty4_params
    ty4_results hmem hB (by rw [toNat_ofNat hq₁, toNat_ofNat hl₁]; exact ⟨by omega, hin⟩)
    (by rw [toNat_ofNat hq₂, toNat_ofNat hl₂]; omega) hg' hS
  rw [toNat_ofNat hq₁, toNat_ofNat hl₁, toNat_ofNat hq₂, toNat_ofNat hl₂] at hres
  simp only [wordsAt, hn₁, hw₂, List.cons.injEq, and_true] at hres
  have hr' := i32_inj hres
  by_contra hn
  simp only [Bool.not_eq_true] at hn
  simp [hn] at hr'
  exact hr hr'

end Silmaril.Proofs.Wasm.Examples.SatAccept.Component
