module

public import Silmaril.Proofs.Wasm.Examples.FarkasAccept.Component.Inst
public import Silmaril.Wasm.Component.Reference.ListLift.Thms
public import Silmaril.Wasm.Component.Reference.ListLift.Bump.Thms
public import Silmaril.Wasm.Acceptor.Abi.Thms
public import Silmaril.Wasm.Acceptor.Bridge.Thms

/-!
# The Farkas acceptor component: soundness of accepting calls

An instance of the acceptor kit (`Silmaril.Wasm.Acceptor`):

* the readers: the system read back from memory (`systemAt`, `ineqAt`, `coeffsAt`,
  `wordsAt64`) are the kit's `listAt`/`pairAt`/`read2` at the canonical-ABI layout of
  `list<ineq>` and `list<s64>` (`reads_ineq`, by the combinators `Reads.list`, `Reads.tuple2`,
  `Reads.record2`, `Reads.map`), and its bounds `IneqsIn` are the kit's `ListIn`;
* `readArgs`: in a store of the acceptor whose ABI memory holds the two arguments
  (`FlatHolds`), the flat arguments, the bounds and the values read back (`flatHolds_read2`);
* `farkasKit`, `checkExport`: the kit of `farkasComp` (instance, bump allocator, invariant) and
  its export `check` with `Goal S y := S ∈ Infeasible`; `checkExport_core`: the Core
  obligation, from `readArgs` and the core soundness theorem
  `Silmaril.Wasm.Examples.FarkasAccept.check_sound`, which holds from any checker state;
* `check_sound`: the kit's `CheckerExport.sound`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Examples.FarkasAccept.Component

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Examples.FarkasAccept
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.ListLift
open Silmaril.Wasm.Acceptor (Reads listAt pairAt read2 enc2 ListIn PairIn NoBounds Kit
  CheckerExport reads_u32 reads_s64 flatHolds_read2)
open Silmaril.Wasm.Logic.Words (wd)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Logic.LinArith.Carrier (IneqW SystemW U32 S64 Infeasible)

/-! ## The readers, as instances of the kit's -/

/-- The reader of a coefficient, `tuple<u32, s64>`. -/
abbrev coeffRd : ByteArray → Nat → U32 × S64 := read2 .u32 .s64 wd wd64

theorem coeffsAt_eq (B : ByteArray) (p n : Nat) : coeffsAt B p n = listAt 16 coeffRd B p n := rfl

theorem systemAt_eq (B : ByteArray) (p n : Nat) : systemAt B p n = listAt 16 ineqAt B p n := rfl

theorem wordsAt64_eq (B : ByteArray) (p n : Nat) : wordsAt64 B p n = listAt 8 wd64 B p n := rfl

theorem ineqsIn_iff (B : ByteArray) (p n : Nat) : IneqsIn B p n ↔ ListIn 16 (PairIn 16) B p n :=
  Iff.rfl

theorem reads_coeff :
    Reads coeffTy ofCoeff coeffRd (Silmaril.Wasm.Acceptor.in2 .u32 .s64 NoBounds NoBounds) :=
  Silmaril.Wasm.Acceptor.Reads.tuple2 reads_u32 reads_s64

/-- **The contract of an `ineq` record**: the record read back, its coefficient block in
bounds. -/
theorem reads_ineq : Reads ineqTy ofIneq ineqAt (PairIn 16) :=
  Silmaril.Wasm.Acceptor.Reads.mono
    (Silmaril.Wasm.Acceptor.Reads.map
      (Silmaril.Wasm.Acceptor.Reads.record2 "ineq" "coeffs" "bound"
        (Silmaril.Wasm.Acceptor.Reads.list reads_coeff) reads_s64)
      (fun c => (⟨c.1, c.2⟩ : IneqW)) (fun r => (r.coeffs, r.bound)) fun _ => rfl)
    fun _ _ h => h.1.1

/-! ## The arguments in memory -/

theorem memBytesOf_acc {s : Store Nat} {top : BitVec 32} {B₁ : ByteArray}
    (hs : AccStore s top B₁) : memBytesOf s 1 = B₁ := by
  obtain ⟨B₀, -, hm⟩ := hs.mems
  simp [memBytesOf, hm]

/-- **The two arguments read back**: in a store of the acceptor whose ABI memory holds the
system and the multipliers, the flat arguments, the bounds and the values. -/
theorem readArgs {S : SystemW} {y : List S64} {s : Store Nat} {top : BitVec 32} {B₁ : ByteArray}
    {lo hi : Nat} {fl : List Core.Val} (hs : AccStore s top B₁)
    (hF : FlatHolds (memBytesOf s 1) lo hi [.list ineqTy, .list .s64] [ofSystem S, ofS64s y] fl) :
    ∃ q₁ q₂, fl = [.i32 (BitVec.ofNat 32 q₁), .i32 (BitVec.ofNat 32 S.length),
        .i32 (BitVec.ofNat 32 q₂), .i32 (BitVec.ofNat 32 y.length)] ∧
      q₁ < 2 ^ 32 ∧ q₂ < 2 ^ 32 ∧ S.length < 2 ^ 32 ∧ y.length < 2 ^ 32 ∧
      IneqsIn B₁ q₁ S.length ∧ systemAt B₁ q₁ S.length = S ∧
      q₂ + 8 * y.length ≤ B₁.size ∧ wordsAt64 B₁ q₂ y.length = y := by
  rw [memBytesOf_acc hs] at hF
  obtain ⟨q₁, q₂, rfl, hq₁, hq₂, hl₁, hl₂, hin₁, hsys, hin₂, hys⟩ :=
    flatHolds_read2 reads_ineq reads_s64 hF
  exact ⟨q₁, q₂, rfl, hq₁, hq₂, hl₁, hl₂, hin₁, hsys, hin₂.1, hys⟩

/-! ## The lowering of the two arguments -/

/-- **The two lowered arguments in memory**: the system and the multipliers, lowered into memory
address `1`, end in a store of the acceptor whose ABI memory holds them. -/
theorem lowered {P : Profile} {S : SystemW} {y : List S64} {s : Store Nat} {fl : List Core.Val}
    (hL : LParams P 3 1 [.list ineqTy, .list .s64] [ofSystem S, ofS64s y] accI.store fl s) :
    ∃ q₁ q₂ top B₁, fl = [.i32 (BitVec.ofNat 32 q₁), .i32 (BitVec.ofNat 32 S.length),
        .i32 (BitVec.ofNat 32 q₂), .i32 (BitVec.ofNat 32 y.length)] ∧
      q₁ < 2 ^ 32 ∧ q₂ < 2 ^ 32 ∧ S.length < 2 ^ 32 ∧ y.length < 2 ^ 32 ∧
      AccStore s top B₁ ∧ IneqsIn B₁ q₁ S.length ∧ systemAt B₁ q₁ S.length = S ∧
      q₂ + 8 * y.length ≤ B₁.size ∧ wordsAt64 B₁ q₂ y.length = y := by
  obtain ⟨t₁, ⟨⟨B₁, hs⟩, -⟩, -, -, hF⟩ := params_holds (farkasBump P) hL fInv_init
  obtain ⟨q₁, q₂, h⟩ := readArgs hs hF
  exact ⟨q₁, q₂, _, B₁, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, hs, h.2.2.2.2.2⟩

/-! ## The kit instance -/

/-- **The kit of `farkasComp`**: the instance `accI`, the bump allocator `farkasBump` for
memory `1`, the invariant `FInv` from `heapBase`. -/
def farkasKit : Kit farkasComp where
  I := accI
  good := farkasComp_good
  inst := farkasComp_inst
  N := memBytes
  Inv := FInv
  bump P := by
    show BumpAlloc P (farkasComp.coreAddr accI "cabi_realloc") 1 memBytes FInv
    rw [t_coreAddrs.1]
    exact farkasBump P
  base := heapBase
  init := fInv_init

theorem checkList_map {α : Type} {t : LTy} {f : α → LVal} (h : ∀ a, t.check (f a) = true) :
    ∀ l : List α, LTy.checkList t (l.map f) = true
  | [] => rfl
  | a :: l => by simp [LTy.checkList, h a, checkList_map h l]

theorem check_ineq (r : IneqW) : ineqTy.check (ofIneq r) = true := by
  have h : ineqTy.check (ofIneq r) = LTy.checkList coeffTy (r.coeffs.map ofCoeff) := by
    simp [ineqTy, ofIneq, LTy.check, LTy.checkFields]
  rw [h]
  exact checkList_map (fun _ => rfl) _

/-- **The export `check`**: an accepting call means that the system is infeasible. -/
def checkExport : CheckerExport farkasComp SystemW (List S64) where
  x := ⟨"check", [("system", .list ineqTy), ("y", .list .s64)], "check"⟩
  mem := List.mem_cons_self
  enc S y := [ofSystem S, ofS64s y]
  typed S y := by
    show LTy.checkParams [.list ineqTy, .list .s64] [ofSystem S, ofS64s y] = true
    simp only [LTy.checkParams, LTy.check, ofSystem, ofS64s, checkList_map check_ineq,
      checkList_map (t := .s64) (f := LVal.s64) (fun _ => rfl), Bool.and_true]
  Goal S y := S ∈ Infeasible ∧ y.length = S.length

/-- **The Core obligation of `check`**, from the core soundness theorem. -/
theorem checkExport_core : checkExport.CoreSound farkasKit := by
  rintro P S y s t fl s' f' r ⟨⟨B₁, hs⟩, -⟩ hF hS hr
  obtain ⟨q₁, q₂, rfl, hq₁, hq₂, hl₁, hl₂, hin, hsys, hb₂, -⟩ := readArgs hs hF
  change Steps _ _ (invoke s (farkasComp.coreAddr accI "check") _) _ at hS
  rw [t_coreAddrs.2] at hS
  have hB := hs.size₁
  have hU := Silmaril.Wasm.Examples.FarkasAccept.check_sound (sp := BitVec.ofNat 32 q₁)
    (sl := BitVec.ofNat 32 S.length) (yp := BitVec.ofNat 32 q₂) (yl := BitVec.ofNat 32 y.length)
    hs (by rw [toNat_ofNat hq₁, toNat_ofNat hl₁]; exact hin)
    (by rw [toNat_ofNat hq₂, toNat_ofNat hl₂]; omega) hS hr
  rw [toNat_ofNat hq₁, toNat_ofNat hl₁, hsys] at hU
  refine ⟨hU.1, ?_⟩
  have := congrArg BitVec.toNat hU.2
  rwa [toNat_ofNat hl₁, toNat_ofNat hl₂] at this

/-! ## The headline result -/

/-- **An accepting call of `check` is on an infeasible system**, whatever the multipliers. -/
theorem check_sound (P : Profile) (prof : ProfileKind) (S : SystemW) (y : List S64)
    (h : Outcome.returns (some [.bool true]) ∈ exportBehaviours prof (refHost P) ()
      farkasComp.toRef [] "check" [(ofSystem S).toRef, (ofS64s y).toRef]) :
    S ∈ Infeasible :=
  (checkExport.sound farkasKit checkExport_core P prof S y h).1

/-- **An accepting call of `check` has one multiplier per inequality.** -/
theorem check_length (P : Profile) (prof : ProfileKind) (S : SystemW) (y : List S64)
    (h : Outcome.returns (some [.bool true]) ∈ exportBehaviours prof (refHost P) ()
      farkasComp.toRef [] "check" [(ofSystem S).toRef, (ofS64s y).toRef]) :
    y.length = S.length :=
  (checkExport.sound farkasKit checkExport_core P prof S y h).2

/-- **Multipliers of the wrong number are never accepted.** -/
theorem check_rejects_length (P : Profile) (prof : ProfileKind) {S : SystemW} {y : List S64}
    (hl : y.length ≠ S.length) :
    Outcome.returns (some [.bool true]) ∉ exportBehaviours prof (refHost P) ()
      farkasComp.toRef [] "check" [(ofSystem S).toRef, (ofS64s y).toRef] :=
  checkExport.rejects farkasKit checkExport_core (R := fun S y => y.length = S.length)
    (fun _ _ h => h.2) P prof hl

end Silmaril.Proofs.Wasm.Examples.FarkasAccept.Component
