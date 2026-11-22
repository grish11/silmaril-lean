module

public import Silmaril.Wasm.Component.Reference.Canon.Lower.Defs
import Silmaril.Wasm.Component.Reference.Canon.Prog.Thms

namespace Silmaril.Proofs.Wasm.Component.Reference.Canon.Lower.StoreLift

open Silmaril.Wasm (AddrType)
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value Silmaril.Wasm.Component.ABI
open Silmaril.Wasm.Component.AsyncRef

variable {E : CoreEngine} {σ α β : Type}

private abbrev Local (program : P E σ α) : Prop := Prog.Every LowerSt.argumentLiftOp program

private theorem pure (value : α) : Local (Prog.pure value : P E σ α) := .pure value

private theorem bind {first : P E σ α} {next : α → P E σ β}
    (localFirst : Local first) (localNext : ∀ value, Local (next value)) :
    Local (first >>= next) := localFirst.bind localNext

private theorem map {program : P E σ α} {project : α → β} (localProgram : Local program) :
    Local (project <$> program) := localProgram.bind fun value => pure (project value)

private theorem ite {test : Prop} [Decidable test] {yes no : P E σ α}
    (localYes : Local yes) (localNo : Local no) : Local (if test then yes else no) := by
  split <;> assumption

private theorem trap (reason : TrapReason) : Local (Canon.trap reason : P E σ α) :=
  .op trivial fun response => nomatch response

private theorem internal (message : String) : Local (Canon.internal message : P E σ α) := trap _

private theorem trapIf (test : Bool) (reason : TrapReason) :
    Local (Canon.trapIf test reason : P E σ Unit) := ite (trap _) (pure ())

private theorem orTrap (reason : TrapReason) (value : Option α) :
    Local (Canon.orTrap reason value : P E σ α) := by
  cases value
  · exact trap _
  · exact pure _

private theorem getStore : Local (Canon.getStore : P E σ (CStore E)) := .lift trivial

private theorem modifyStore (update : CStore E → CStore E)
    (preserves : ∀ store caller, LowerSt.callerShape (update store) caller = LowerSt.callerShape store caller) :
    Local (Canon.modifyStore update : P E σ Unit) := .lift preserves

private theorem getObj {Key : Type} (field : ArenaField E Key α) (index : Key) :
    Local (Canon.getObj field index : P E σ α) := bind getStore fun _ => orTrap _ _

private theorem ptrType (cx : LiftLowerContext E) : Local (Canon.ptrType cx : P E σ _) :=
  bind getStore fun _ => pure _

private theorem memAddr (cx : LiftLowerContext E) : Local (Canon.memAddr cx : P E σ _) :=
  orTrap _ _

private theorem readMem (cx : LiftLowerContext E) (ptr length : Nat) :
    Local (Canon.readMem cx ptr length : P E σ ByteArray) :=
  bind (memAddr cx) fun _ => bind getStore fun _ => orTrap _ _

private theorem checkInBounds (cx : LiftLowerContext E) (ptr length : Nat) :
    Local (Canon.checkInBounds cx ptr length : P E σ Unit) :=
  bind (bind (memAddr cx) fun _ => bind getStore fun _ => orTrap _ _) fun _ => trapIf _ _

private theorem loadInt (cx : LiftLowerContext E) (ptr length : Nat) (signed : Bool) :
    Local (Canon.loadInt cx ptr length signed : P E σ Int) :=
  bind (readMem cx ptr length) fun _ => pure _

private theorem convertI32ToChar (bits : BitVec 32) :
    Local (Canon.convertI32ToChar bits : P E σ Char) := orTrap _ _

private theorem loadStringFromRange (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
    (ptr tagged : Nat) : Local (Canon.loadStringFromRange lim q cx ptr tagged : P E σ StrVal) := by
  unfold Canon.loadStringFromRange
  refine bind (ptrType cx) fun _ => bind (trapIf _ _) fun _ => bind (trapIf _ _) fun _ =>
    bind (checkInBounds _ _ _) fun _ => bind (readMem _ _ _) fun _ => ?_
  split
  · exact trap _
  · exact pure _

private theorem loadString (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (ptr : Nat) :
    Local (Canon.loadString lim q cx ptr : P E σ StrVal) :=
  bind (bind (ptrType cx) fun _ => pure _) fun _ =>
    bind (map (readMem _ _ _)) fun _ => bind (map (readMem _ _ _)) fun _ =>
      loadStringFromRange _ _ _ _ _

private theorem handlesGet (inst : InstId) (index : Nat) :
    Local (Canon.handlesGet inst index : P E σ HandleEntry) :=
  bind (getObj _ _) fun _ => orTrap _ _

private theorem handlesRemove (inst : InstId) (index : Nat) :
    Local (Canon.handlesRemove inst index : P E σ HandleEntry) := by
  unfold Canon.handlesRemove
  refine bind (getObj _ _) fun _ => ?_
  split
  · exact trap _
  · exact bind (modifyStore _ (fun _ _ => rfl)) fun _ => pure _

private theorem expectResource (entry : HandleEntry) :
    Local (Canon.expectResource entry : P E σ HandleObjId) := by
  cases entry <;> first | exact pure _ | exact trap _

private theorem liftOwn (lim : Limits) (cx : LiftLowerContext E) (rt : RtId) (index : Nat) :
    Local (Canon.liftOwn lim cx rt index : P E σ Nat) :=
  bind (handlesRemove _ _) fun _ => bind (expectResource _) fun _ => bind (getObj _ _) fun _ =>
    bind (trapIf _ _) fun _ => bind (trapIf _ _) fun _ => bind (trapIf _ _) fun _ => pure _

private theorem liftBorrow (lim : Limits) (cx : LiftLowerContext E) (rt : RtId) (index : Nat) :
    Local (Canon.liftBorrow lim cx rt index : P E σ Nat) := by
  unfold Canon.liftBorrow
  split
  · exact bind (handlesGet _ _) fun _ => bind (expectResource _) fun _ => bind (getObj _ _) fun _ =>
      bind (trapIf _ _) fun _ => bind (modifyStore _ (fun _ _ => rfl)) fun _ => pure _
  · exact internal _

private theorem liftAsyncValue (lim : Limits) (kind : EndKind) (cx : LiftLowerContext E)
    (type : Option (WIT.ClosedType RtId)) (index : Nat) :
    Local (Canon.liftAsyncValue lim kind cx type index : P E σ EndId) := by
  have checked (entry : HandleEntry) : Local (checkLiftEnd kind type entry : P E σ EndId) := by
    unfold checkLiftEnd
    split
    · exact bind (getObj _ _) fun _ => bind (trapIf _ _) fun _ => bind (trapIf _ _) fun _ =>
        bind (trapIf _ _) fun _ => bind (trapIf _ _) fun _ => pure _
    · exact trap _
  exact bind (handlesRemove _ _) fun _ => bind (checked _) fun _ => bind (modifyStore _ (fun _ _ => rfl)) fun _ => pure _

private theorem liftErrorContext (lim : Limits) (cx : LiftLowerContext E) (index : Nat) :
    Local (Canon.liftErrorContext lim cx index : P E σ ErrCtxId) :=
  bind (handlesGet _ _) fun entry => by cases entry <;> first | exact pure _ | exact trap _

private theorem loadPtrWord (cx : LiftLowerContext E) (p : AddrType) (ptr : Nat) :
    Local (Canon.loadPtrWord cx p ptr : P E σ Nat) :=
  bind (loadInt _ _ _ _) fun _ => pure _

private theorem loadPrim (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
    (prim : WIT.Primitive) (ptr : Nat) :
    Local (Canon.loadPrim lim q cx prim ptr : P E σ Val) := by
  cases prim
  case char =>
    exact bind (loadInt _ _ _ _) fun _ => bind (convertI32ToChar _) fun _ => pure _
  case string => exact bind (loadString _ _ _ _) fun _ => pure _
  all_goals exact bind (loadInt _ _ _ _) fun _ => pure _

private theorem loadListFromValidRangeWith {f : Nat → P E σ Val} (hf : ∀ n, Local (f n))
    (ptr length sz : Nat) :
    Local (Canon.loadListFromValidRangeWith f ptr length sz) :=
  Prog.Every.mapM fun _ _ => hf _

private theorem loadListFromRangeWith (lim : Limits) (cx : LiftLowerContext E) (l : Layout)
    {f : Nat → P E σ Val} (hf : ∀ n, Local (f n)) (ptr length : Nat) :
    Local (Canon.loadListFromRangeWith lim cx l f ptr length) :=
  bind (trapIf _ _) fun _ => bind (trapIf _ _) fun _ => bind (checkInBounds _ _ _) fun _ =>
    loadListFromValidRangeWith hf _ _ _

private theorem loadListWith (lim : Limits) (cx : LiftLowerContext E) (p : AddrType) (l : Layout)
    {f : Nat → P E σ Val} (hf : ∀ n, Local (f n)) (ptr : Nat) :
    Local (Canon.loadListWith lim cx p l f ptr) :=
  bind (loadPtrWord _ _ _) fun _ => bind (loadPtrWord _ _ _) fun _ =>
    loadListFromRangeWith lim cx l hf _ _

private theorem loadVariantWith (cx : LiftLowerContext E) (n : Nat) (a : Alignment)
    {payload : Nat → Nat → P E σ (Option Val)} (hp : ∀ i ptr, Local (payload i ptr))
    (ptr : Nat) : Local (Canon.loadVariantWith cx n a payload ptr) :=
  bind (loadInt _ _ _ _) fun _ => bind (trapIf _ _) fun _ => bind (hp _ _) fun _ => pure _

private theorem loadFlags (cx : LiftLowerContext E) (ptr : Nat) (labels : List String) :
    Local (Canon.loadFlags cx ptr labels : P E σ Val) :=
  bind (loadInt _ _ _ _) fun _ => pure _

private theorem loadMapEntryWith (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (p : AddrType)
    (k : WIT.KeyType) (lv : Layout) {fv : Nat → P E σ Val} (hv : ∀ n, Local (fv n))
    (ptr : Nat) : Local (Canon.loadMapEntryWith lim q cx p k lv fv ptr) :=
  bind (loadPrim _ _ _ _ _) fun _ => bind (hv _) fun _ => pure _

mutual
  private theorem loadAt (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
      (p : AddrType) : (t : WIT.ClosedType RtId) → (ptr : Nat) →
      Local (Canon.loadAt lim q cx p t ptr : P E σ Val)
    | .prim prim, ptr => by simp only [Canon.loadAt, Canon.loadAtWith]; exact loadPrim _ _ _ _ _
    | .ref r, _ => nomatch r
    | .list t, ptr => by
      simp only [Canon.loadAt, Canon.loadAtWith]
      exact bind (loadListWith _ _ _ _ (loadAt lim q cx p t) _) fun _ => pure _
    | .fixedList t n, ptr => by
      simp only [Canon.loadAt, Canon.loadAtWith]
      exact bind (loadListFromValidRangeWith (loadAt lim q cx p t) _ _ _) fun _ => pure _
    | .record fields, ptr => by
      simp only [Canon.loadAt, Canon.loadAtWith]
      exact bind (loadFieldsAt lim q cx p fields ptr) fun _ => pure _
    | .tuple ts, ptr => by
      simp only [Canon.loadAt, Canon.loadAtWith]
      exact bind (loadTypesAt lim q cx p ts ptr) fun _ => pure _
    | .variant cases, ptr => by
      simp only [Canon.loadAt, Canon.loadAtWith]
      exact loadVariantWith _ _ _ (loadCaseAt lim q cx p cases) _
    | .enum labels, ptr => by
      simp only [Canon.loadAt, Canon.loadAtWith]
      exact loadVariantWith _ _ _ (fun _ _ => pure _) _
    | .flags labels, ptr => by simp only [Canon.loadAt, Canon.loadAtWith]; exact loadFlags _ _ _
    | .option t, ptr => by
      simp only [Canon.loadAt, Canon.loadAtWith]
      refine loadVariantWith _ _ _ (fun i _ => ?_) _
      rcases i with _ | _ | _
      · exact pure _
      · exact bind (loadAt lim q cx p t _) fun _ => pure _
      · exact pure _
    | .result ok err, ptr => by
      simp only [Canon.loadAt, Canon.loadAtWith]
      refine loadVariantWith _ _ _ (fun i _ => ?_) _
      rcases i with _ | _ | _
      · exact loadOptAt lim q cx p ok _
      · exact loadOptAt lim q cx p err _
      · exact pure _
    | .map k v, ptr => by
      simp only [Canon.loadAt, Canon.loadAtWith]
      exact bind (loadListWith _ _ _ _
        (loadMapEntryWith _ _ _ _ _ _ (loadAt lim q cx p v)) _) fun _ => pure _
    | .own rt, ptr => by
      simp only [Canon.loadAt, Canon.loadAtWith]
      exact bind (loadInt _ _ _ _) fun _ => bind (liftOwn _ _ _ _) fun _ => pure _
    | .borrow rt, ptr => by
      simp only [Canon.loadAt, Canon.loadAtWith]
      exact bind (loadInt _ _ _ _) fun _ => bind (liftBorrow _ _ _ _) fun _ => pure _
    | .stream t, ptr => by
      simp only [Canon.loadAt, Canon.loadAtWith]
      exact bind (loadInt _ _ _ _) fun _ =>
        bind (liftAsyncValue _ _ _ _ _) fun _ => pure _
    | .future t, ptr => by
      simp only [Canon.loadAt, Canon.loadAtWith]
      exact bind (loadInt _ _ _ _) fun _ =>
        bind (liftAsyncValue _ _ _ _ _) fun _ => pure _
    | .errorContext, ptr => by
      simp only [Canon.loadAt, Canon.loadAtWith]
      exact bind (loadInt _ _ _ _) fun _ => bind (liftErrorContext _ _ _) fun _ => pure _

  private theorem loadFieldsAt (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
      (p : AddrType) : (fields : List (String × WIT.ClosedType RtId)) → (ptr : Nat) →
      Local (Canon.loadFieldsAt lim q cx p fields ptr : P E σ (List Val))
    | [], _ => by simp only [Canon.loadFieldsAt, Canon.loadFieldsAtWith]; exact pure _
    | (_, t) :: fields, ptr => by
      simp only [Canon.loadFieldsAt, Canon.loadFieldsAtWith]
      exact bind (loadAt lim q cx p t _) fun _ =>
        bind (loadFieldsAt lim q cx p fields _) fun _ => pure _

  private theorem loadTypesAt (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
      (p : AddrType) : (ts : List (WIT.ClosedType RtId)) → (ptr : Nat) →
      Local (Canon.loadTypesAt lim q cx p ts ptr : P E σ (List Val))
    | [], _ => by simp only [Canon.loadTypesAt, Canon.loadTypesAtWith]; exact pure _
    | t :: ts, ptr => by
      simp only [Canon.loadTypesAt, Canon.loadTypesAtWith]
      exact bind (loadAt lim q cx p t _) fun _ =>
        bind (loadTypesAt lim q cx p ts _) fun _ => pure _

  private theorem loadCaseAt (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
      (p : AddrType) : (cases : List (String × Option (WIT.ClosedType RtId))) → (i ptr : Nat) →
      Local (Canon.loadCaseAt lim q cx p cases i ptr : P E σ (Option Val))
    | [], _, _ => by simp only [Canon.loadCaseAt, Canon.loadCaseAtWith]; exact pure _
    | (_, t) :: _, 0, ptr => by
      simp only [Canon.loadCaseAt, Canon.loadCaseAtWith]
      exact loadOptAt lim q cx p t ptr
    | _ :: cases, i + 1, ptr => by
      simp only [Canon.loadCaseAt, Canon.loadCaseAtWith]
      exact loadCaseAt lim q cx p cases i ptr

  private theorem loadOptAt (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
      (p : AddrType) : (t : Option (WIT.ClosedType RtId)) → (ptr : Nat) →
      Local (Canon.loadOptAt lim q cx p t ptr : P E σ (Option Val))
    | none, _ => by simp only [Canon.loadOptAt, Canon.loadOptAtWith]; exact pure _
    | some t, ptr => by
      simp only [Canon.loadOptAt, Canon.loadOptAtWith]
      exact bind (loadAt lim q cx p t ptr) fun _ => pure _
end

private theorem next (vi : FlatCursor) (t : CoreType) :
    Local (FlatCursor.next vi t : P E σ _) := by
  unfold FlatCursor.next
  split
  · exact pure _
  · exact internal _

private theorem nextN (vi : FlatCursor) (ts : List CoreType) :
    Local (FlatCursor.nextN vi ts : P E σ _) := by
  induction ts generalizing vi with
  | nil => exact pure _
  | cons t ts ih => exact bind (next vi t) fun _ => bind (ih _) fun _ => pure _


private theorem liftFlatPrim (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (p : AddrType)
    (prim : WIT.Primitive) (vi : FlatCursor) :
    Local (Canon.liftFlatPrim lim q cx p prim vi : P E σ _) := by
  unfold Canon.liftFlatPrim
  cases prim
  case bool | f32 | f64 => exact bind (next _ _) fun _ => pure _
  case char => exact bind (next _ _) fun _ => bind (convertI32ToChar _) fun _ => pure _
  case string =>
    exact bind (next _ _) fun _ => bind (next _ _) fun _ =>
      bind (loadStringFromRange _ _ _ _ _) fun _ => pure _
  all_goals exact bind (next _ _) fun _ => pure _

private theorem liftFlatN {f : FlatCursor → P E σ (Val × FlatCursor)} (hf : ∀ vi, Local (f vi))
    (n : Nat) (vi : FlatCursor) : Local (Canon.liftFlatN f n vi) := by
  induction n generalizing vi with
  | zero => exact pure _
  | succ n ih => exact bind (hf _) fun _ => bind (ih _) fun _ => pure _

private theorem liftFlatListWith (lim : Limits) (cx : LiftLowerContext E) (p : AddrType) (l : Layout)
    {f : Nat → P E σ Val} (hf : ∀ n, Local (f n)) (vi : FlatCursor) :
    Local (Canon.liftFlatListWith lim cx p l f vi) :=
  bind (next _ _) fun _ => bind (next _ _) fun _ =>
    bind (loadListFromRangeWith lim cx l hf _ _) fun _ => pure _

private theorem liftFlatVariantWith (n : Nat) (joined : List CoreType) (wants : Nat → List CoreType)
    {payload : Nat → FlatCursor → P E σ (Option Val × FlatCursor)}
    (hp : ∀ i c, Local (payload i c)) (vi : FlatCursor) :
    Local (Canon.liftFlatVariantWith n joined wants payload vi) :=
  bind (next _ _) fun _ => bind (trapIf _ _) fun _ => bind (nextN _ _) fun _ =>
    bind (hp _ _) fun _ => pure _

mutual
  private theorem liftFlatAt (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
      (p : AddrType) : (t : WIT.ClosedType RtId) → (vi : FlatCursor) →
      Local (Canon.liftFlatAt lim q cx p t vi : P E σ _)
    | .prim prim, vi => by rw [Canon.liftFlatAt, Canon.liftFlatAtWith]; exact liftFlatPrim _ _ _ _ _ _
    | .ref r, _ => nomatch r
    | .list t, vi => by
      rw [Canon.liftFlatAt, Canon.liftFlatAtWith]; exact liftFlatListWith _ _ _ _ (loadAt lim q cx p t) _
    | .fixedList t n, vi => by
      rw [Canon.liftFlatAt, Canon.liftFlatAtWith]
      exact bind (liftFlatN (liftFlatAt lim q cx p t) _ _) fun _ => pure _
    | .record fields, vi => by
      rw [Canon.liftFlatAt, Canon.liftFlatAtWith]
      exact bind (liftFlatFields lim q cx p fields vi) fun _ => pure _
    | .tuple ts, vi => by
      rw [Canon.liftFlatAt, Canon.liftFlatAtWith]
      exact bind (liftFlatTypes lim q cx p ts vi) fun _ => pure _
    | .variant cases, vi => by
      rw [Canon.liftFlatAt, Canon.liftFlatAtWith]
      exact liftFlatVariantWith _ _ _ (liftFlatCaseAt lim q cx p cases) _
    | .enum labels, vi => by
      rw [Canon.liftFlatAt, Canon.liftFlatAtWith]
      exact liftFlatVariantWith _ _ _ (fun _ _ => pure _) _
    | .flags labels, vi => by
      rw [Canon.liftFlatAt, Canon.liftFlatAtWith]; exact bind (next _ _) fun _ => pure _
    | .option t, vi => by
      rw [Canon.liftFlatAt, Canon.liftFlatAtWith]
      refine liftFlatVariantWith _ _ _ (fun i _ => ?_) _
      rcases i with _ | _ | _
      · exact pure _
      · exact bind (liftFlatAt lim q cx p t _) fun _ => pure _
      · exact pure _
    | .result ok err, vi => by
      rw [Canon.liftFlatAt, Canon.liftFlatAtWith]
      refine liftFlatVariantWith _ _ _ (fun i _ => ?_) _
      rcases i with _ | _ | _
      · exact liftFlatOpt lim q cx p ok _
      · exact liftFlatOpt lim q cx p err _
      · exact pure _
    | .map k v, vi => by
      rw [Canon.liftFlatAt, Canon.liftFlatAtWith]
      exact liftFlatListWith _ _ _ _
        (loadMapEntryWith _ _ _ _ _ _ (loadAt lim q cx p v)) _
    | .own rt, vi => by
      rw [Canon.liftFlatAt, Canon.liftFlatAtWith]
      exact bind (next _ _) fun _ => bind (map (liftOwn _ _ _ _)) fun _ => pure _
    | .borrow rt, vi => by
      rw [Canon.liftFlatAt, Canon.liftFlatAtWith]
      exact bind (next _ _) fun _ => bind (map (liftBorrow _ _ _ _)) fun _ => pure _
    | .stream t, vi => by
      rw [Canon.liftFlatAt, Canon.liftFlatAtWith]
      exact bind (next _ _) fun _ =>
        bind (map (liftAsyncValue _ _ _ _ _)) fun _ => pure _
    | .future t, vi => by
      rw [Canon.liftFlatAt, Canon.liftFlatAtWith]
      exact bind (next _ _) fun _ =>
        bind (map (liftAsyncValue _ _ _ _ _)) fun _ => pure _
    | .errorContext, vi => by
      rw [Canon.liftFlatAt, Canon.liftFlatAtWith]
      exact bind (next _ _) fun _ => bind (map (liftErrorContext _ _ _)) fun _ => pure _

  private theorem liftFlatFields (lim : Limits) (q : Quirks)
      (cx : LiftLowerContext E) (p : AddrType) :
      (fields : List (String × WIT.ClosedType RtId)) → (vi : FlatCursor) →
      Local (Canon.liftFlatFields lim q cx p fields vi : P E σ _)
    | [], _ => by rw [Canon.liftFlatFields, Canon.liftFlatFieldsWith]; exact pure _
    | (_, t) :: fields, vi => by
      rw [Canon.liftFlatFields, Canon.liftFlatFieldsWith]
      exact bind (liftFlatAt lim q cx p t _) fun _ =>
        bind (liftFlatFields lim q cx p fields _) fun _ => pure _

  private theorem liftFlatTypes (lim : Limits) (q : Quirks)
      (cx : LiftLowerContext E) (p : AddrType) :
      (ts : List (WIT.ClosedType RtId)) → (vi : FlatCursor) →
      Local (Canon.liftFlatTypes lim q cx p ts vi : P E σ _)
    | [], _ => by rw [Canon.liftFlatTypes, Canon.liftFlatTypesWith]; exact pure _
    | t :: ts, vi => by
      rw [Canon.liftFlatTypes, Canon.liftFlatTypesWith]
      exact bind (liftFlatAt lim q cx p t _) fun _ =>
        bind (liftFlatTypes lim q cx p ts _) fun _ => pure _

  private theorem liftFlatCaseAt (lim : Limits) (q : Quirks)
      (cx : LiftLowerContext E) (p : AddrType) :
      (cases : List (String × Option (WIT.ClosedType RtId))) → (i : Nat) →
      (vi : FlatCursor) →
      Local (Canon.liftFlatCaseAt lim q cx p cases i vi : P E σ _)
    | [], _, _ => by rw [Canon.liftFlatCaseAt, Canon.liftFlatCaseAtWith]; exact pure _
    | (_, t) :: _, 0, vi => by rw [Canon.liftFlatCaseAt, Canon.liftFlatCaseAtWith]; exact liftFlatOpt lim q cx p t vi
    | _ :: cases, i + 1, vi => by
      rw [Canon.liftFlatCaseAt, Canon.liftFlatCaseAtWith]; exact liftFlatCaseAt lim q cx p cases i vi

  private theorem liftFlatOpt (lim : Limits) (q : Quirks)
      (cx : LiftLowerContext E) (p : AddrType) :
      (t : Option (WIT.ClosedType RtId)) → (vi : FlatCursor) →
      Local (Canon.liftFlatOpt lim q cx p t vi : P E σ _)
    | none, _ => by rw [Canon.liftFlatOpt, Canon.liftFlatOptWith]; exact pure _
    | some t, vi => by
      rw [Canon.liftFlatOpt, Canon.liftFlatOptWith]; exact bind (liftFlatAt lim q cx p t vi) fun _ => pure _
end

private theorem liftFlatValues (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
    (max : Nat) (vi : FlatCursor) (ts : List (WIT.ClosedType RtId)) :
    Local (Canon.liftFlatValues lim q cx max vi ts : P E σ _) :=
  bind (ptrType cx) fun p =>
    ite (bind (next _ _) fun _ => bind (trapIf _ _) fun _ => bind (checkInBounds _ _ _)
      fun _ => bind (loadTypesAt lim q cx p ts _) fun _ => pure _)
      (liftFlatTypes lim q cx p ts vi)

private theorem maybeOnProgress (subtask : SubtaskId) :
    Local (Canon.maybeOnProgress subtask : P E σ Unit) :=
  bind (getObj _ _) fun _ => ite (modifyStore _ (fun _ _ => rfl)) (pure ())

private theorem callerShape_setPos (store : CStore E) (caller observed : CallerId) (pos : Nat) :
    LowerSt.callerShape (LowerSt.setCallerPosSt caller pos store) observed = LowerSt.callerShape store observed := by
  unfold LowerSt.callerShape LowerSt.setCallerPosSt CStore.caller?
  rw [ArenaField.get?_modify]
  split
  · cases ArenaField.callers.get? store observed with
    | none => rfl
    | some record => cases record <;> rfl
  · rfl

public theorem lowerOnStart_caller_shape (lim : Limits) (q : Quirks) (caller : CallerId) :
    Prog.Every LowerSt.argumentLiftOp (Canon.lowerOnStart lim q caller : P E σ (List Val)) := by
  unfold Canon.lowerOnStart
  refine bind (getObj _ _) fun record => ?_
  cases record with
  | lower subtask cx args pos ft limit results =>
    exact bind (maybeOnProgress subtask) fun _ => bind (modifyStore _ (fun _ _ => rfl)) fun _ =>
      bind (liftFlatValues lim q cx limit ⟨args, pos⟩ _) fun (_, next) =>
        bind (modifyStore _ (fun store observed => callerShape_setPos store caller observed next.pos)) fun _ => pure _
  | host => exact internal _
  | sub => exact internal _

public theorem lowerOnStart_every (lim : Limits) (q : Quirks) (caller : CallerId)
    {allow : Op E σ → Prop} (get : allow .get) (modify : ∀ update, allow (.modify update))
    (fail : ∀ reason, allow (.trap reason)) :
    Prog.Every (S := Eff E σ) allow (Canon.lowerOnStart lim q caller) := by
  have weaken {α : Type} {program : P E σ α} (localProgram : Local program) :
      Prog.Every (S := Eff E σ) allow program := by
    induction localProgram with
    | pure value => exact .pure value
    | @op op _ allowed _ ih =>
      refine .op ?_ ih
      cases op <;> first | exact get | exact modify _ | exact fail _ | exact False.elim allowed
  exact weaken (lowerOnStart_caller_shape lim q caller)

end Silmaril.Proofs.Wasm.Component.Reference.Canon.Lower.StoreLift
