module

public import Silmaril.Proofs.Wasm.Component.Reference.ListLift.StoreList

/-!
# Accepting runs of the lowering of `ListLift` values

The reference lowering of the fragment's values in a lowering context of the caller
(`LowerCx`), on an accepting path, is the Core-level relation of
`Silmaril.Wasm.Component.Reference.ListLift` on the renamed core stores:

* `spec_store_s32`, `spec_store_list`: the canonical ABI `store` of an `s32` element (one
  `memWrite?` of its `le32` bytes) and of a nested list (`store_list_into_range`, then the
  `(ptr, len)` pair), the two element cases of `LStore`; `spec_store` combines them by recursion
  on the type;
* `spec_lowerFlatTypes`, `spec_lowerParams`: the flat lowering of the parameters (`LParams`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.ListLift

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Reference.ListLift
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile} {prof : ProfileKind}

/-! ## Values -/

theorem toRefList_eq_map : ∀ vs : List LVal, LVal.toRefList vs = vs.map LVal.toRef
  | [] => rfl
  | v :: vs => by
    simp only [LVal.toRefList, List.map_cons, toRefList_eq_map vs]

theorem checkList_mem {t : LTy} : ∀ {vs : List LVal}, LTy.checkList t vs = true →
    ∀ v ∈ vs, t.check v = true
  | [], _, _, h => nomatch h
  | v :: vs, h, u, hu => by
    simp only [LTy.checkList, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hu with rfl | hu
    · exact h.1
    · exact checkList_mem h.2 u hu

/-- The layout of an element type: alignment `4`, size `LTy.size`. -/
theorem layout_toClosed (t : LTy) :
    (ABI.layout .i32 t.toClosed).alignment.bytes = 4 ∧
      (ABI.layout .i32 t.toClosed).size = t.size := by
  cases t <;> simp [LTy.toClosed, LTy.size, ABI.layout, ABI.primitiveLayout,
    ABI.pointerLayout, ABI.pointerAlignment, ABI.Layout.size, ABI.Alignment.bytes]

/-- The bytes `store_int` writes for an `s32`. -/
theorem intToLE_s32 (x : BitVec 32) : intToLE 4 x.toInt = le32 x := by
  unfold intToLE le32
  rw [show 8 * 4 = 32 from rfl, BitVec.toInt_emod_two_pow, Int.toNat_natCast]

/-- The bytes `store_int` writes for a pointer-sized number. -/
theorem intToLE_nat (q : Nat) : intToLE 4 (q : Int) = le32 (BitVec.ofNat 32 q) := by
  unfold intToLE le32
  rw [BitVec.toNat_ofNat]
  congr 1

/-! ## Element stores -/

theorem store_s32 (cx : LiftLowerContext (E3 P)) (x : BitVec 32) (a : Nat) :
    (Canon.store Limits.spec Quirks.none cx (.int .s32 x.toInt) (.prim .s32) a :
      Canon.P (E3 P) Unit Unit) = writeMem cx a (intToLE 4 x.toInt) := by
  rw [Canon.store.eq_def]
  rfl

theorem store_list (cx : LiftLowerContext (E3 P)) (vs : List Value.Val)
    (u : WIT.ClosedType RtId) (a : Nat) :
    (Canon.store Limits.spec Quirks.none cx (.list vs) (.list u) a : Canon.P (E3 P) Unit Unit) =
      (ptrType cx >>= fun p => storeListWith cx (ABI.layout p u)
        (fun e a => Canon.store Limits.spec Quirks.none cx e u a) false vs a) := by
  rw [Canon.store.eq_def]

/-- The pointer type of a lowering context is `i32`. -/
theorem ptrTypeIn_i32 {I : Silmaril.Wasm.Game.ScalarInstance} {ra ma : Nat}
    {cx : LiftLowerContext (E3 P)} (hcx : LowerCx P I ra ma cx) {m : Config (E3 P) Unit}
    (hi : LInv P I ma m) : ptrTypeIn m.store cx = .i32 := by
  simp [ptrTypeIn, CanonOpts.ptrType, hcx.mem, hi.mem]

/-- A store that changes only the core store keeps the caller records and tasks. -/
theorem Grows.core (m : Config (E3 P) Unit) (c' : (E3 P).Store (CanonHost (E3 P))) :
    Grows m { m with store := { m.store with core := c' } } :=
  ⟨List.prefix_refl _, List.prefix_refl _⟩

/-- **The `s32` element store.** -/
theorem spec_store_s32 {I : Silmaril.Wasm.Game.ScalarInstance} {ra ma : Nat} {th : Option ThreadId}
    {cx : LiftLowerContext (E3 P)} (hcx : LowerCx P I ra ma cx) (x : BitVec 32) :
    ElemSpec prof P I ma th LVal.toRef
      (fun e a => Canon.store Limits.spec Quirks.none cx e LTy.s32.toClosed a)
      (LStore P ra ma .s32) (.s32 x) := by
  intro a m hi
  show SpecR prof P th (Canon.store Limits.spec Quirks.none cx (.int .s32 x.toInt) (.prim .s32) a)
    m _
  rw [store_s32]
  refine Spec.mono (spec_writeMem hcx.mem _ _) fun _ m' ⟨c', hw, hm⟩ _ _ => ?_
  subst m'
  obtain ⟨hi', hm'⟩ := hi.write hw
  rw [intToLE_s32] at hm'
  exact ⟨hi', Grows.core _ _, .s32 hm'⟩

/-- `storeInt` of a pointer-sized number. -/
theorem spec_storeInt_nat {th : Option ThreadId} {ma : Nat} {cx : LiftLowerContext (E3 P)}
    (hcx : cx.opts.memory = some (memAt P ma)) {m : Config (E3 P) Unit} (q a : Nat) :
    SpecR prof P th (storeInt cx (q : Int) a 4) m
      (fun _ m' => ∃ c', Silmaril.Wasm.SingleThreaded.memWrite? m.store.core ma a
        (le32 (BitVec.ofNat 32 q)) = some c' ∧
        m' = { m with store := { m.store with core := c' } }) := by
  unfold storeInt
  rw [intToLE_nat]
  exact spec_writeMem hcx _ _

/-- The elements of a list, stored by `LStore`. -/
theorem elems_of {ra ma : Nat} {t : LTy} {us : List LVal} {p : Nat}
    {s s' : Silmaril.Wasm.Execution.Core.Store Nat}
    (h : ElemsRel t.size (LStore P ra ma t) us p s s') : LElems P ra ma t us p s s' := by
  induction h with
  | nil => exact .nil
  | cons he _ ih => exact .cons he ih

/-- **`store_list_into_range` of a list of values of type `t`** at the element layout of `t`:
the Core-level `LList`, given the element store of `t`. -/
theorem spec_storeListL {I : Silmaril.Wasm.Game.ScalarInstance} {ra ma : Nat} {th : Option ThreadId}
    {cx : LiftLowerContext (E3 P)} (hcx : LowerCx P I ra ma cx) (t : LTy) (us : List LVal)
    (hel : ∀ u ∈ us, ElemSpec prof P I ma th LVal.toRef
      (fun e a => Canon.store Limits.spec Quirks.none cx e t.toClosed a) (LStore P ra ma t) u)
    {m : Config (E3 P) Unit} (hi : LInv P I ma m) :
    SpecR prof P th (storeListIntoRangeWith cx (ABI.layout .i32 t.toClosed)
      (fun e a => Canon.store Limits.spec Quirks.none cx e t.toClosed a) (us.map LVal.toRef)) m
      (fun r m' => LInv P I ma m' ∧ Grows m m' ∧ ∃ q, r = (q, us.length) ∧
        LList P ra ma t us (cmap m.store) q (cmap m'.store)) := by
  obtain ⟨hal, hsz⟩ := layout_toClosed t
  refine Spec.mono (spec_storeListIntoRange hcx _ LVal.toRef _ _ us hel hi)
    fun r m' ⟨hi', hg', q, s₁, hr, hrun, hq, hb, he⟩ _ _ => ⟨hi', hg', q, hr, ?_⟩
  rw [hal, hsz] at hrun
  rw [hal] at hq
  rw [hsz] at hb he
  exact .mk hrun hq hb (elems_of he)

/-- **The nested list element store**, given the element store of its element type. -/
theorem spec_store_list {I : Silmaril.Wasm.Game.ScalarInstance} {ra ma : Nat} {th : Option ThreadId}
    {cx : LiftLowerContext (E3 P)} (hcx : LowerCx P I ra ma cx) (t : LTy) (us : List LVal)
    (hel : ∀ u ∈ us, ElemSpec prof P I ma th LVal.toRef
      (fun e a => Canon.store Limits.spec Quirks.none cx e t.toClosed a) (LStore P ra ma t) u) :
    ElemSpec prof P I ma th LVal.toRef
      (fun e a => Canon.store Limits.spec Quirks.none cx e (LTy.list t).toClosed a)
      (LStore P ra ma (.list t)) (.list us) := by
  intro a m hi
  show SpecR prof P th (Canon.store Limits.spec Quirks.none cx (.list (LVal.toRefList us))
    (.list t.toClosed) a) m _
  rw [store_list, toRefList_eq_map]
  refine Spec.bind (Spec.gets _) fun p m₁ ⟨hp, hm⟩ _ _ => ?_
  subst m₁
  rw [ptrTypeIn_i32 hcx hi] at hp
  subst hp
  unfold storeListWith
  refine Spec.ite_false rfl ?_
  refine Spec.bind (spec_storeListL hcx t us hel hi) fun r m₂ ⟨hi₂, hg₂, q, hr, hl⟩ _ _ => ?_
  subst r
  dsimp only
  unfold ptrSize
  refine Spec.bind (Spec.bind (Spec.gets _) fun p m₃ ⟨hp, hm⟩ _ _ => ?_)
    (R := fun sz m' => sz = 4 ∧ m' = m₂) fun sz m₄ ⟨hsz, hm⟩ _ _ => ?_
  · subst m₃
    rw [ptrTypeIn_i32 hcx hi₂] at hp
    subst hp
    exact Spec.mono (Spec.pure _) fun sz m' ⟨hsz, hm⟩ _ _ => ⟨hsz, hm⟩
  subst m₄ sz
  refine Spec.bind (spec_storeInt_nat hcx.mem q a) fun _ m₅ ⟨c₁, hw₁, hm⟩ _ _ => ?_
  subst m₅
  obtain ⟨hi₅, hm₁⟩ := hi₂.write hw₁
  refine Spec.mono (spec_storeInt_nat hcx.mem us.length (a + 4))
    fun _ m' ⟨c₂, hw₂, hm⟩ _ _ => ?_
  subst m'
  obtain ⟨hi', hm₂⟩ := hi₅.write hw₂
  refine ⟨hi', hg₂.trans ((Grows.core _ _).trans (Grows.core _ _)), ?_⟩
  exact .list hl hm₁ hm₂

/-- **Element stores of the fragment's types**, by recursion on the type. -/
theorem spec_store {I : Silmaril.Wasm.Game.ScalarInstance} {ra ma : Nat} {th : Option ThreadId}
    {cx : LiftLowerContext (E3 P)} (hcx : LowerCx P I ra ma cx) :
    ∀ (t : LTy) (v : LVal), t.check v = true → ElemSpec prof P I ma th LVal.toRef
      (fun e a => Canon.store Limits.spec Quirks.none cx e t.toClosed a) (LStore P ra ma t) v
  | .s32, .s32 x, _ => spec_store_s32 hcx x
  | .list t, .list us, h => spec_store_list hcx t us fun u hu =>
    spec_store hcx t u (checkList_mem h u hu)
  | .s32, .list _, h => nomatch h
  | .list _, .s32 _, h => nomatch h

/-! ## Parameters -/

theorem lowerFlatAt_s32 (cx : LiftLowerContext (E3 P)) (x : BitVec 32) :
    (lowerFlatAt Limits.spec Quirks.none cx .i32 (.int .s32 x.toInt) (.prim .s32) :
      Canon.P (E3 P) Unit (List FlatValue)) = Prog.pure [⟨.int .i32, x⟩] := by
  show Prog.pure [lowerFlatInt .s32 x.toInt] = _
  have e : lowerFlatInt .s32 x.toInt = (⟨.int .i32, x⟩ : FlatValue) := by
    show (⟨.int .i32, BitVec.ofInt 32 x.toInt⟩ : FlatValue) = ⟨.int .i32, x⟩
    rw [BitVec.ofInt_toInt]
  rw [e]

/-- **The flat lowering of the parameters** (`lower_flat` of each, left to right). -/
theorem spec_lowerFlatTypes {I : Silmaril.Wasm.Game.ScalarInstance} {ra ma : Nat}
    {th : Option ThreadId} {cx : LiftLowerContext (E3 P)} (hcx : LowerCx P I ra ma cx) :
    ∀ (ts : List LTy) (vs : List LVal), LTy.checkParams ts vs = true →
    ∀ (m : Config (E3 P) Unit), LInv P I ma m →
      SpecR prof P th (lowerFlatTypes Limits.spec Quirks.none cx .i32 (vs.map LVal.toRef)
        (ts.map LTy.toClosed)) m
        (fun fl m' => LInv P I ma m' ∧ Grows m m' ∧
          LParams P ra ma ts vs (cmap m.store) (fl.map Silmaril.Wasm.SingleThreaded.ofFlat)
            (cmap m'.store))
  | [], [], _, m, hi => Spec.mono (Spec.pure _) fun fl m' ⟨hfl, hm⟩ _ _ => by
      subst fl m'
      exact ⟨hi, Grows.refl _, .nil⟩
  | .s32 :: ts, .s32 x :: vs, h, m, hi => by
    simp only [LTy.checkParams, LTy.check, Bool.true_and] at h
    show SpecR prof P th (lowerFlatAt Limits.spec Quirks.none cx .i32 (.int .s32 x.toInt)
      (.prim .s32) >>= fun a => lowerFlatTypes Limits.spec Quirks.none cx .i32 (vs.map LVal.toRef)
        (ts.map LTy.toClosed) >>= fun b => pure (a ++ b)) m _
    rw [lowerFlatAt_s32]
    refine Spec.bind (Spec.pure _) fun a m₁ ⟨ha, hm⟩ _ _ => ?_
    subst a m₁
    refine Spec.bind (spec_lowerFlatTypes hcx ts vs h m hi) fun b m₂ ⟨hi₂, hg₂, hp₂⟩ _ _ => ?_
    refine Spec.mono (Spec.pure _) fun fl m' ⟨hfl, hm⟩ _ _ => ?_
    subst fl m'
    exact ⟨hi₂, hg₂, .s32 hp₂⟩
  | .list t :: ts, .list us :: vs, h, m, hi => by
    simp only [LTy.checkParams, LTy.check, Bool.and_eq_true] at h
    show SpecR prof P th ((storeListIntoRange Limits.spec Quirks.none cx (LVal.toRefList us)
      t.toClosed >>= fun r => match r with
        | (ptr, len) => pure [ptrFlat .i32 ptr, ptrFlat .i32 len]) >>= fun a =>
      lowerFlatTypes Limits.spec Quirks.none cx .i32 (vs.map LVal.toRef)
        (ts.map LTy.toClosed) >>= fun b => pure (a ++ b)) m _
    unfold storeListIntoRange
    rw [toRefList_eq_map]
    simp only [bind_assoc]
    refine Spec.bind (Spec.gets _) fun p m₁ ⟨hp, hm⟩ _ _ => ?_
    subst m₁
    rw [ptrTypeIn_i32 hcx hi] at hp
    subst hp
    refine Spec.bind (spec_storeListL hcx t us
      (fun u hu => spec_store hcx t u (checkList_mem h.1 u hu)) hi)
      fun r m₂ ⟨hi₂, hg₂, q, hr, hl⟩ _ _ => ?_
    subst r
    refine Spec.bind (Spec.pure _) fun a m₃ ⟨ha, hm⟩ _ _ => ?_
    subst a m₃
    refine Spec.bind (spec_lowerFlatTypes hcx ts vs h.2 m₂ hi₂)
      fun b m₄ ⟨hi₄, hg₄, hp₄⟩ _ _ => ?_
    refine Spec.mono (Spec.pure _) fun fl m' ⟨hfl, hm⟩ _ _ => ?_
    subst fl m'
    exact ⟨hi₄, hg₂.trans hg₄, .list hl hp₄⟩
  | [], _ :: _, h, _, _ => nomatch h
  | _ :: _, [], h, _, _ => nomatch h
  | .s32 :: _, .list _ :: _, h, _, _ => by simp [LTy.checkParams, LTy.check] at h
  | .list _ :: _, .s32 _ :: _, h, _, _ => by simp [LTy.checkParams, LTy.check] at h

theorem flatten_length (t : LTy) : (ABI.flatten .i32 t.toClosed).length ≤ 2 := by
  cases t <;> simp [LTy.toClosed, ABI.flatten, ABI.flattenPrimitive]

theorem flattenTypes_length : ∀ ts : List LTy,
    (ABI.flattenTypes .i32 (ts.map LTy.toClosed)).length ≤ 2 * ts.length
  | [] => by simp [ABI.flattenTypes]
  | t :: ts => by
    have h₁ := flatten_length t
    have h₂ := flattenTypes_length ts
    simp only [List.map_cons, ABI.flattenTypes, List.length_append, List.length_cons]
    omega

/-- **The flat lowering of the parameters** by `lower_flat_values` (at most `16` flat
values: no spilling). -/
theorem spec_lowerParams {I : Silmaril.Wasm.Game.ScalarInstance} {ra ma : Nat}
    {th : Option ThreadId} {cx : LiftLowerContext (E3 P)} (hcx : LowerCx P I ra ma cx)
    (ts : List LTy) (hts : 2 * ts.length ≤ 16) (vs : List LVal)
    (hvs : LTy.checkParams ts vs = true) {m : Config (E3 P) Unit} (hi : LInv P I ma m) :
    SpecR prof P th (lowerFlatValues Limits.spec Quirks.none cx ABI.maxFlatParams
      (vs.map LVal.toRef) (ts.map LTy.toClosed) none) m
      (fun fl m' => LInv P I ma m' ∧ Grows m m' ∧
        LParams P ra ma ts vs (cmap m.store) (fl.map Silmaril.Wasm.SingleThreaded.ofFlat)
          (cmap m'.store)) := by
  unfold lowerFlatValues
  refine Spec.bind (Spec.gets _) fun p m₁ ⟨hp, hm⟩ _ _ => ?_
  subst m₁
  rw [ptrTypeIn_i32 hcx hi] at hp
  subst hp
  split
  · next h =>
    have := flattenTypes_length ts
    exact absurd h (by unfold ABI.maxFlatParams; omega)
  · exact spec_lowerFlatTypes hcx ts vs hvs m hi

end Silmaril.Proofs.Wasm.Component.Reference.ListLift
