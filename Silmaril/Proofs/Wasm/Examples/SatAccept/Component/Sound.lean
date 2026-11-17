module

public import Silmaril.Proofs.Wasm.Examples.SatAccept.Component.Inst
public import Silmaril.Wasm.Component.Reference.ListLift.Thms
public import Silmaril.Wasm.Component.Reference.ListLift.Bump.Thms
public import Silmaril.Logic.SAT.Carrier.Thms
public import Silmaril.Wasm.Acceptor.Abi.Thms
public import Silmaril.Wasm.Acceptor.Bridge.Thms

/-!
# The SAT acceptor component: soundness of accepting calls

An instance of the acceptor kit (`Silmaril.Wasm.Acceptor`):

* `lower2`, `holdsL_nested`: the lowering of the two arguments ends with them in memory
  (`params_holds` with `satBump`, read by the kit's `flatHolds_two`), and a lowered
  `list<list<s32>>` reads back as `nestedAt` with its blocks in bounds (`holdsL_listAt` with
  `reads_words`);
* `satKit`, `streamExport`, `nestedExport`: the kit of `satComp` (instance, bump allocator,
  invariant `SInv`) and its two exports, with `Goal xs ms := satStream xs ms = true` and
  `Goal p ms := satNested p ms = true`; `streamExport_core`, `nestedExport_core`: the Core
  obligations, from the kit's `flatHolds_read2` and the core function's specification
  (`stream_returns`, `nested_returns`: the answer is `1` exactly when the checker accepts);
* `checkStream_sound`, `checkNested_sound`: the kit's `CheckerExport.sound`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Examples.SatAccept.Component

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation Silmaril.Wasm.Game
open Silmaril.Wasm.Examples.SatAccept
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.ListLift
open Silmaril.Wasm.Acceptor (Kit CheckerExport reads_s32 reads_words flatHolds_two flatHolds_read2
  holdsL_listAt checkList_map)
open Silmaril.Wasm.Logic.Words (wd words MemAt)
open Silmaril.Wasm.Logic.VC (globalVal)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Logic.SAT.Carrier (satStream satNested)

/-! ## Reading the arguments -/

/-- **The clauses of a `list<list<s32>>` are the words of their blocks** (the kit's
`holdsL_listAt` at `reads_words`). -/
theorem holdsL_nested {B : ByteArray} {lo hi : Nat} (p : List (List (BitVec 32))) (q : Nat)
    (h : HoldsL B lo hi (.list .s32) (p.map LVal.ofWords) q) :
    nestedAt B q p.length = p ∧
      ∀ i < p.length, (wd B (q + 8 * i)).toNat + 4 * (wd B (q + 8 * i + 4)).toNat ≤ B.size :=
  holdsL_listAt reads_words p q h

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
  obtain ⟨q₁, q₂, rfl, hq₁, hq₂, hl₁, hl₂, hb₁, hL₁, hb₂, hL₂⟩ := flatHolds_two hF
  simp only [List.length_map, LTy.size_s32] at hl₂ hb₂ ⊢
  obtain ⟨hw, -⟩ := holdsL_listAt reads_s32 ms q₂ hL₂
  exact ⟨q₁, q₂, mt, B, heapBase, t₁, rfl, hq₁, hq₂, hl₁, hl₂, hf, hm, hB, by rw [hg]; rfl,
    hb₁, hL₁, by omega, hw⟩

theorem toNat_ofNat {q : Nat} (h : q < 2 ^ 32) : (BitVec.ofNat 32 q).toNat = q := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-! ## The kit instance -/

/-- **The kit of `satComp`**: the instance `satI`, the bump allocator `satBump` for memory `0`,
the invariant `SInv` from `heapBase`. -/
def satKit : Kit satComp where
  I := satI
  good := satComp_good
  inst := satComp_inst
  N := memBytes
  Inv := SInv
  bump P := by
    show BumpAlloc P (satComp.coreAddr satI "cabi_realloc") 0 memBytes SInv
    rw [t_coreAddrs.1]
    exact satBump P
  base := heapBase
  init := sInv_init

theorem check_words (xs : List (BitVec 32)) : (LTy.list .s32).check (LVal.ofWords xs) = true := by
  simp only [LVal.ofWords, LTy.check]
  exact checkList_map (t := .s32) (f := LVal.s32) (fun _ => rfl) xs

/-- **The export `check-stream`**: an accepting call means that `satStream` accepts. -/
def streamExport : CheckerExport satComp (List (BitVec 32)) (List (BitVec 32)) where
  x := ⟨"check-stream", [("problem", .list .s32), ("model", .list .s32)], "check-stream"⟩
  mem := List.mem_cons_self
  enc xs ms := [LVal.ofWords xs, LVal.ofWords ms]
  typed xs ms := by
    show LTy.checkParams [.list .s32, .list .s32] [LVal.ofWords xs, LVal.ofWords ms] = true
    simp only [LTy.checkParams, check_words, Bool.and_true]
  Goal xs ms := satStream xs ms = true

/-- **The export `check-nested`**: an accepting call means that `satNested` accepts. -/
def nestedExport : CheckerExport satComp (List (List (BitVec 32))) (List (BitVec 32)) where
  x := ⟨"check-nested", [("problem", .list (.list .s32)), ("model", .list .s32)], "check-nested"⟩
  mem := List.mem_cons_of_mem _ List.mem_cons_self
  enc p ms := [LVal.ofNested p, LVal.ofWords ms]
  typed p ms := by
    show LTy.checkParams [.list (.list .s32), .list .s32] [LVal.ofNested p, LVal.ofWords ms] = true
    simp only [LTy.checkParams, LVal.ofNested, LTy.check, check_words, checkList_map check_words,
      Bool.and_true]
  Goal p ms := satNested p ms = true

/-- The answer of a check is `1` exactly when the checker accepts; a nonzero answer is `1`. -/
theorem accepts_of_res {b : Bool} {r : BitVec 32}
    (hres : [Val.i32 r] = [Val.i32 (if b then 1 else 0)]) (hr : r ≠ 0) : b = true := by
  simp only [List.cons.injEq, and_true] at hres
  have hr' := i32_inj hres
  by_contra hn
  simp only [Bool.not_eq_true] at hn
  simp [hn] at hr'
  exact hr hr'

/-- **The Core obligation of `check-stream`**, from `stream_returns`. -/
theorem streamExport_core : streamExport.CoreSound satKit := by
  rintro P xs ms s t fl s' f' r ⟨hf, ⟨mt, B, hm, hB⟩, hg, -⟩ hF hS hr
  change FlatHolds (memBytesOf s 0) heapBase t [.list .s32, .list .s32]
    [LVal.ofWords xs, LVal.ofWords ms] fl at hF
  have hBm : memBytesOf s 0 = B := by simp [memBytesOf, hm]
  rw [hBm] at hF
  obtain ⟨q₁, q₂, rfl, hq₁, hq₂, hl₁, hl₂, hin₁, hw₁, hin₂, hw₂⟩ :=
    flatHolds_read2 reads_s32 reads_s32 hF
  change Steps _ _ (invoke s (satComp.coreAddr satI "check-stream") _) _ at hS
  rw [t_coreAddrs.2.1] at hS
  obtain ⟨f₀, f₁, f₂, hF, -, hc₁, -, -, he₁, -, -, hm₁, -, hg₀, hg₁, -⟩ := funcs_eq
  have hfi : s.funcs[1]? = some f₁ := by rw [hf, hF]; rfl
  have hmem : MemAt s f₁.module 0 mt B := ⟨by rw [hm₁]; rfl, hm⟩
  have hg' : (globalVal s f₁.module 0).isSome := by
    rw [globalVal_congr (m' := satM) (by rw [satM_eq hF, hg₁, hg₀]) 0, hg]
    rfl
  have h₁ : q₁ + 4 * xs.length ≤ B.size := hin₁.1
  have h₂ : q₂ + 4 * ms.length ≤ B.size := hin₂.1
  obtain ⟨-, hres⟩ := stream_returns (pp := BitVec.ofNat 32 q₁) (pl := BitVec.ofNat 32 xs.length)
    (mp := BitVec.ofNat 32 q₂) (ml := BitVec.ofNat 32 ms.length) hfi hc₁ he₁ ty4_params
    ty4_results hmem hB (by rw [toNat_ofNat hq₁, toNat_ofNat hl₁]; omega)
    (by rw [toNat_ofNat hq₂, toNat_ofNat hl₂]; omega) hg' hS
  rw [toNat_ofNat hq₁, toNat_ofNat hl₁, toNat_ofNat hq₂, toNat_ofNat hl₂,
    show wordsAt B q₁ xs.length = xs from hw₁, show wordsAt B q₂ ms.length = ms from hw₂] at hres
  exact accepts_of_res hres hr

/-- **The Core obligation of `check-nested`**, from `nested_returns`. -/
theorem nestedExport_core : nestedExport.CoreSound satKit := by
  rintro P p ms s t fl s' f' r ⟨hf, ⟨mt, B, hm, hB⟩, hg, -⟩ hF hS hr
  change FlatHolds (memBytesOf s 0) heapBase t [.list (.list .s32), .list .s32]
    [LVal.ofNested p, LVal.ofWords ms] fl at hF
  have hBm : memBytesOf s 0 = B := by simp [memBytesOf, hm]
  rw [hBm] at hF
  obtain ⟨q₁, q₂, rfl, hq₁, hq₂, hl₁, hl₂, hin₁, hn₁, hin₂, hw₂⟩ :=
    flatHolds_read2 reads_words reads_s32 hF
  change Steps _ _ (invoke s (satComp.coreAddr satI "check-nested") _) _ at hS
  rw [t_coreAddrs.2.2] at hS
  obtain ⟨f₀, f₁, f₂, hF, -, -, hc₁, -, -, he₁, -, -, hm₁, hg₀, -, hg₁⟩ := funcs_eq
  have hfi : s.funcs[2]? = some f₂ := by rw [hf, hF]; rfl
  have hmem : MemAt s f₂.module 0 mt B := ⟨by rw [hm₁]; rfl, hm⟩
  have hg' : (globalVal s f₂.module 0).isSome := by
    rw [globalVal_congr (m' := satM) (by rw [satM_eq hF, hg₁, hg₀]) 0, hg]
    rfl
  have h₂ : q₂ + 4 * ms.length ≤ B.size := hin₂.1
  obtain ⟨-, hres⟩ := nested_returns (pp := BitVec.ofNat 32 q₁) (pl := BitVec.ofNat 32 p.length)
    (mp := BitVec.ofNat 32 q₂) (ml := BitVec.ofNat 32 ms.length) hfi hc₁ he₁ ty4_params
    ty4_results hmem hB (by rw [toNat_ofNat hq₁, toNat_ofNat hl₁]; exact hin₁)
    (by rw [toNat_ofNat hq₂, toNat_ofNat hl₂]; omega) hg' hS
  rw [toNat_ofNat hq₁, toNat_ofNat hl₁, toNat_ofNat hq₂, toNat_ofNat hl₂,
    show nestedAt B q₁ p.length = p from hn₁, show wordsAt B q₂ ms.length = ms from hw₂] at hres
  exact accepts_of_res hres hr

/-! ## The headline results -/

/-- **An accepting call of `check-stream` answers `satStream`.** -/
theorem checkStream_sound (P : Profile) (prof : ProfileKind) (xs ms : List (BitVec 32))
    (h : Outcome.returns (some [.bool true]) ∈ exportBehaviours prof (refHost P) () satComp.toRef
      [] "check-stream" [(LVal.ofWords xs).toRef, (LVal.ofWords ms).toRef]) :
    satStream xs ms = true :=
  streamExport.sound satKit streamExport_core P prof xs ms h

/-- **An accepting call of `check-nested` answers `satNested`.** -/
theorem checkNested_sound (P : Profile) (prof : ProfileKind) (p : List (List (BitVec 32)))
    (ms : List (BitVec 32))
    (h : Outcome.returns (some [.bool true]) ∈ exportBehaviours prof (refHost P) () satComp.toRef
      [] "check-nested" [(LVal.ofNested p).toRef, (LVal.ofWords ms).toRef]) :
    satNested p ms = true :=
  nestedExport.sound satKit nestedExport_core P prof p ms h

end Silmaril.Proofs.Wasm.Examples.SatAccept.Component
