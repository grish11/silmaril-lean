module

public import Silmaril.Proofs.Wasm.Examples.FarkasAccept.Component.Inst
public import Silmaril.Wasm.Component.Reference.ListLift.Thms
public import Silmaril.Wasm.Component.Reference.ListLift.Bump.Thms

/-!
# The Farkas acceptor component: soundness of accepting calls

An accepting call of `check` has, by `acceptSound farkasComp`, a Core-level explanation: the
lowering `LParams` of the two lists into memory address `1` from the instance store to a store
`s`, and a run of the core function from `s` returning a nonzero `i32`. The lowering ends in a
store of the acceptor (`AccStore`, `params_holds` with the bump allocator `farkasBump`) with the
arguments in its ABI memory, read back field by field (`holdsL_system`, `holdsL_s64s`: the
records at their canonical-ABI offsets are `systemAt`, the multipliers `wordsAt64`), so the core
soundness theorem `Silmaril.Wasm.Examples.FarkasAccept.check_sound` puts the system in
`Infeasible`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Examples.FarkasAccept.Component

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Examples.FarkasAccept
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.ListLift
open Silmaril.Wasm.Logic.Words (wd)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Logic.LinArith.Carrier (IneqW SystemW U32 S64 Infeasible)

/-! ## Reading the lowered values -/

theorem coeffsAt_succ (B : ByteArray) (p n : Nat) :
    coeffsAt B p (n + 1) = (wd B p, dw B (p + 8)) :: coeffsAt B (p + 16) n := by
  unfold coeffsAt
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, Nat.succ_eq_add_one]
  rw [show p + 16 * (i + 1) = p + 16 + 16 * i by omega]

theorem wordsAt64_succ (B : ByteArray) (p n : Nat) :
    wordsAt64 B p (n + 1) = dw B p :: wordsAt64 B (p + 8) n := by
  unfold wordsAt64
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, Nat.succ_eq_add_one]
  rw [show p + 8 * (i + 1) = p + 8 + 8 * i by omega]

theorem systemAt_succ (B : ByteArray) (p n : Nat) :
    systemAt B p (n + 1) = ineqAt B p :: systemAt B (p + 16) n := by
  unfold systemAt
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, Nat.succ_eq_add_one]
  rw [show p + 16 * (i + 1) = p + 16 + 16 * i by omega]

/-- **The multipliers of a lowered `list<s64>` are the 64-bit words of their block.** -/
theorem holdsL_s64s {B : ByteArray} {lo hi : Nat} :
    ∀ (y : List S64) (q : Nat), HoldsL B lo hi .s64 (y.map .s64) q → wordsAt64 B q y.length = y
  | [], _, _ => rfl
  | a :: y, q, h => by
    have h' : (q + 8 ≤ B.size ∧ wd64 B q = a) ∧ HoldsL B lo hi .s64 (y.map .s64) (q + 8) := h
    rw [List.length_cons, wordsAt64_succ, holdsL_s64s y (q + 8) h'.2]
    exact congrArg (· :: y) h'.1.2

/-- **The coefficients of a lowered `list<tuple<u32, s64>>`.** -/
theorem holdsL_coeffs {B : ByteArray} {lo hi : Nat} :
    ∀ (cs : List (U32 × S64)) (q : Nat), HoldsL B lo hi coeffTy (cs.map ofCoeff) q →
      coeffsAt B q cs.length = cs
  | [], _, _ => rfl
  | c :: cs, q, h => by
    have h' : ((q + 4 ≤ B.size ∧ wd B q = c.1) ∧ (q + 8 + 8 ≤ B.size ∧ wd64 B (q + 8) = c.2) ∧
        True) ∧ HoldsL B lo hi coeffTy (cs.map ofCoeff) (q + 16) := h
    obtain ⟨⟨⟨-, h₁⟩, ⟨-, h₂⟩, -⟩, hr⟩ := h'
    rw [List.length_cons, coeffsAt_succ, holdsL_coeffs cs (q + 16) hr]
    have e₂ : dw B (q + 8) = c.2 := h₂
    rw [h₁, e₂]

/-- **An inequality record in memory**: the record at `p` is `r`, and its coefficient block lies
in memory. -/
theorem holds_ineq {B : ByteArray} {lo hi : Nat} (r : IneqW) (p : Nat)
    (h : Holds B lo hi ineqTy (ofIneq r) p) :
    ineqAt B p = r ∧ (wd B p).toNat + 16 * (wd B (p + 4)).toNat ≤ B.size := by
  obtain ⟨cs, b⟩ := r
  have h' : Holds B lo hi (.list coeffTy) (.list (cs.map ofCoeff)) p ∧
      Holds B lo hi .s64 (.s64 b) (p + 8) ∧ True := h
  obtain ⟨hl, ⟨-, hb⟩, -⟩ := h'
  simp only [Holds, List.length_map] at hl
  obtain ⟨-, hlen, -, -, hB, hc⟩ := hl
  have hsz : coeffTy.size = 16 := rfl
  rw [hsz] at hB
  refine ⟨?_, by rw [hlen]; omega⟩
  unfold ineqAt
  rw [hlen, holdsL_coeffs cs _ hc]
  have e : dw B (p + 8) = b := hb
  rw [e]

/-- **The system of a lowered `list<ineq>`**: the records at `q` are `S`, and every coefficient
block lies in memory. -/
theorem holdsL_system {B : ByteArray} {lo hi : Nat} :
    ∀ (S : SystemW) (q : Nat), HoldsL B lo hi ineqTy (S.map ofIneq) q →
      systemAt B q S.length = S ∧
        ∀ i < S.length, (wd B (q + 16 * i)).toNat + 16 * (wd B (q + 16 * i + 4)).toNat ≤ B.size
  | [], _, _ => ⟨rfl, by simp⟩
  | r :: S, q, h => by
    have h' : Holds B lo hi ineqTy (ofIneq r) q ∧ HoldsL B lo hi ineqTy (S.map ofIneq) (q + 16) :=
      h
    obtain ⟨hr₁, hr₂⟩ := holds_ineq r q h'.1
    obtain ⟨ih₁, ih₂⟩ := holdsL_system S (q + 16) h'.2
    refine ⟨by rw [List.length_cons, systemAt_succ, hr₁, ih₁], fun i hi => ?_⟩
    cases i with
    | zero => simpa using hr₂
    | succ i =>
      have := ih₂ i (by simp only [List.length_cons] at hi; omega)
      rw [show q + 16 * (i + 1) = q + 16 + 16 * i by omega]
      exact this

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
  have hBm : memBytesOf s 1 = B₁ := by
    obtain ⟨B₀, -, hm⟩ := hs.mems
    simp [memBytesOf, hm]
  rw [hBm] at hF
  have hi : ineqTy.size = 16 := rfl
  have h8 : LTy.s64.size = 8 := rfl
  simp only [FlatHolds, ofSystem, ofS64s, List.length_map, hi, h8] at hF
  obtain ⟨q₁, fl₁, rfl, hq₁, hl₁, -, -, hb₁, hL₁, q₂, fl₂, rfl, hq₂, hl₂, -, -, hb₂, hL₂, rfl⟩ :=
    hF
  obtain ⟨hsys, hin⟩ := holdsL_system S q₁ hL₁
  refine ⟨q₁, q₂, _, B₁, rfl, hq₁, hq₂, hl₁, hl₂, hs, ⟨by omega, hin⟩, hsys, by omega,
    holdsL_s64s y q₂ hL₂⟩

theorem checkList_map {α : Type} {t : LTy} {f : α → LVal} (h : ∀ a, t.check (f a) = true) :
    ∀ l : List α, LTy.checkList t (l.map f) = true
  | [] => rfl
  | a :: l => by simp [LTy.checkList, h a, checkList_map h l]

theorem check_ineq (r : IneqW) : ineqTy.check (ofIneq r) = true := by
  have h : ineqTy.check (ofIneq r) = LTy.checkList coeffTy (r.coeffs.map ofCoeff) := by
    simp [ineqTy, ofIneq, LTy.check, LTy.checkFields]
  rw [h]
  exact checkList_map (fun _ => rfl) _

/-! ## The headline result -/

/-- **An accepting call of `check` is on an infeasible system**, whatever the multipliers. -/
theorem check_sound (P : Profile) (prof : ProfileKind) (S : SystemW) (y : List S64)
    (h : Outcome.returns (some [.bool true]) ∈ exportBehaviours prof (refHost P) ()
      farkasComp.toRef [] "check" [(ofSystem S).toRef, (ofS64s y).toRef]) :
    S ∈ Infeasible := by
  have hx : (⟨"check", [("system", .list ineqTy), ("y", .list .s64)], "check"⟩ : ListExport) ∈
      farkasComp.exports := List.mem_cons_self
  have hc : LTy.checkParams [.list ineqTy, .list .s64] [ofSystem S, ofS64s y] = true := by
    simp only [LTy.checkParams, LTy.check, ofSystem, ofS64s, checkList_map check_ineq,
      checkList_map (t := .s64) (f := LVal.s64) (fun _ => rfl), Bool.and_true]
  obtain ⟨s, fl, s', f', r, hL, hS, hr⟩ :=
    acceptSound farkasComp P prof accI farkasComp_good farkasComp_inst _ hx _ hc h
  change LParams P (farkasComp.coreAddr accI "cabi_realloc") 1 [.list ineqTy, .list .s64] _
    accI.store fl s at hL
  change Steps _ _ (invoke s (farkasComp.coreAddr accI "check") fl) _ at hS
  rw [t_coreAddrs.1] at hL
  rw [t_coreAddrs.2] at hS
  obtain ⟨q₁, q₂, top, B₁, rfl, hq₁, hq₂, hl₁, hl₂, hs, hin, hsys, hb₂, -⟩ := lowered hL
  have hB := hs.size₁
  have hU := Silmaril.Wasm.Examples.FarkasAccept.check_sound (sp := BitVec.ofNat 32 q₁)
    (sl := BitVec.ofNat 32 S.length) (yp := BitVec.ofNat 32 q₂) (yl := BitVec.ofNat 32 y.length)
    hs (by rw [toNat_ofNat hq₁, toNat_ofNat hl₁]; exact hin)
    (by rw [toNat_ofNat hq₂, toNat_ofNat hl₂]; omega) hS hr
  rw [toNat_ofNat hq₁, toNat_ofNat hl₁, hsys] at hU
  exact hU

end Silmaril.Proofs.Wasm.Examples.FarkasAccept.Component
