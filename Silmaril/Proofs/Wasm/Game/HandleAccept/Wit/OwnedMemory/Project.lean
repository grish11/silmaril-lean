module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Resources.Thms

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory

open Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value
  Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory
open Silmaril.Wasm.Game.HandleAccept.Wit
open Silmaril.Wasm (AddrType)

variable {E : CoreEngine} {World : Type}

private theorem projectBind {α β γ δ : Type} (eraseIn : α → β) (eraseOut : γ → δ)
    {before : P E World α} {after : P E World β} {left : α → P E World γ}
    {right : β → P E World δ} (first : eraseIn <$> before = after)
    (next : ∀ input, eraseOut <$> left input = right (eraseIn input)) :
    eraseOut <$> (before >>= left) = after >>= right := by
  rw [map_bind, ← first, bind_map_left]
  exact congrArg (fun cont => before >>= cont) (funext next)

private theorem fixedBind {α β γ : Type} (erase : β → γ) {step : P E World α}
    {left : α → P E World β} {right : α → P E World γ}
    (next : ∀ input, erase <$> left input = right input) :
    erase <$> (step >>= left) = step >>= right := by
  rw [map_bind]
  exact congrArg (fun cont => step >>= cont) (funext next)

private theorem projectList {α : Type} {left : α → P E World Observed}
    {right : α → P E World Val} (agree : ∀ input, Observed.value <$> left input = right input)
    (inputs : List α) :
    List.map Observed.value <$> Prog.mapM left inputs = Prog.mapM right inputs := by
  induction inputs with
  | nil => simp only [Prog.mapM_nil, ← Prog.pure_eq, map_pure, List.map_nil]
  | cons head tail ih =>
    simp only [Prog.mapM_cons]
    exact projectBind Observed.value (List.map Observed.value) (agree head) fun _ =>
      projectBind (List.map Observed.value) (List.map Observed.value) ih fun _ => rfl

private theorem projectRange (limits : Limits) (cx : LiftLowerContext E) (layout : Layout)
    {left : Nat → P E World Observed} {right : Nat → P E World Val}
    (agree : ∀ ptr, Observed.value <$> left ptr = right ptr) (ptr len : Nat) :
    List.map Observed.value <$> loadListFromRangeWith limits cx layout left ptr len =
      loadListFromRangeWith limits cx layout right ptr len := by
  unfold loadListFromRangeWith loadListFromValidRangeWith
  exact fixedBind _ fun _ => fixedBind _ fun _ => fixedBind _ fun _ => projectList (fun _ => agree _) _

private theorem projectItems (limits : Limits) (cx : LiftLowerContext E) (width : AddrType)
    (layout : Layout) {left : Nat → P E World Observed} {right : Nat → P E World Val}
    (agree : ∀ ptr, Observed.value <$> left ptr = right ptr) (ptr : Nat) :
    List.map Observed.value <$> loadListWith limits cx width layout left ptr =
      loadListWith limits cx width layout right ptr := by
  unfold loadListWith
  exact fixedBind _ fun base => fixedBind _ fun len => projectRange limits cx layout agree base len

private theorem projectVariant (cx : LiftLowerContext E) (count : Nat) (alignment : Alignment)
    {left : Nat → Nat → P E World (Option Observed)} {right : Nat → Nat → P E World (Option Val)}
    (agree : ∀ index ptr, Option.map Observed.value <$> left index ptr = right index ptr) (ptr : Nat) :
    Observed.value <$> loadVariantUsing cx count alignment Observed.variant left ptr =
      loadVariantWith cx count alignment right ptr := by
  unfold loadVariantUsing loadVariantWith
  exact fixedBind _ fun discr => fixedBind _ fun _ =>
    projectBind (Option.map Observed.value) Observed.value (agree discr.toNat _) fun _ => rfl

private theorem ordinary_value (action : P E World Val) :
    Observed.value <$> (Observed.ordinary <$> action) = action := by
  rw [Functor.map_map]
  exact id_map action

private theorem own_value (cx : LiftLowerContext E) (resource : RtId) (slot : Nat) :
    Observed.value <$> (Resources.takeWith cx resource slot (Observed.own resource) :
      P E World Observed) = (do return .own (← liftOwn Limits.spec cx resource slot)) := by
  change (Resources.takeWith cx resource slot (Observed.own resource)).bind
    (fun value => Prog.pure value.value) = _
  simp only [Resources.takeWith, liftOwn, Observed.own, Prog.bind_eq,
    Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind']

variable (limits : Limits) (quirks : Quirks) (cx : LiftLowerContext E) (width : AddrType)

local notation "ownerCarrier" => carrier (World := World) limits quirks cx
local notation "readOwned" => loadAtWith limits cx width ownerCarrier
local notation "readVal" => loadAt (σ := World) limits quirks cx width

mutual
  theorem project : ∀ (type : WIT.ClosedType RtId) (ptr : Nat),
      Observed.value <$> readOwned type ptr = readVal type ptr
    | .prim prim, ptr => by
      simp only [loadAt, loadAtWith]; exact ordinary_value _
    | .ref impossible, _ => nomatch impossible
    | .list item, ptr => by
      simp only [loadAt, loadAtWith]
      exact projectBind (List.map Observed.value) Observed.value
        (projectItems limits cx width _ (project item) ptr) (fun _ => rfl)
    | .fixedList item count, ptr => by
      simp only [loadAt, loadAtWith, loadListFromValidRangeWith]
      exact projectBind (List.map Observed.value) Observed.value
        (projectList (fun _ => project item _) (List.range count))
        (fun _ => rfl)
    | .record fields, ptr => by
      simp only [loadAt, loadAtWith]
      exact projectBind (List.map Observed.value) Observed.value (projectFields fields ptr)
        (fun _ => rfl)
    | .tuple types, ptr => by
      simp only [loadAt, loadAtWith]
      exact projectBind (List.map Observed.value) Observed.value (projectTypes types ptr)
        (fun _ => rfl)
    | .variant cases, ptr => by
      simp only [loadAt, loadAtWith]
      exact projectVariant cx _ _ (projectCases cases) ptr
    | .enum labels, ptr => by
      simp only [loadAt, loadAtWith]
      exact projectVariant cx _ _ (fun _ _ => rfl) ptr
    | .flags labels, ptr => by
      simp only [loadAt, loadAtWith]; exact ordinary_value _
    | .option item, ptr => by
      simp only [loadAt, loadAtWith]
      apply projectVariant
      intro index addr
      cases index with
      | zero => rfl
      | succ index =>
        cases index with
        | zero =>
          exact projectBind Observed.value (Option.map Observed.value) (project item addr) (fun _ => rfl)
        | succ _ => rfl
    | .result ok err, ptr => by
      simp only [loadAt, loadAtWith]
      apply projectVariant
      intro index addr
      cases index with
      | zero => exact projectOptional ok addr
      | succ index =>
        cases index with
        | zero => exact projectOptional err addr
        | succ _ => rfl
    | .map key item, ptr => by
      simp only [loadAt, loadAtWith]
      refine projectBind (List.map Observed.value) Observed.value
        (projectItems limits cx width _ ?_ ptr) (fun _ => rfl)
      intro addr
      unfold loadMapEntryUsing
      refine projectBind Observed.value Observed.value (ordinary_value _) fun _ =>
        projectBind Observed.value Observed.value (project item _) fun _ => ?_
      rfl
    | .own resource, ptr => by
      simp only [loadAt, loadAtWith]
      exact fixedBind _ fun bits => own_value cx resource bits.toNat
    | .borrow resource, ptr => by
      simp only [loadAt, loadAtWith]; exact ordinary_value _
    | .stream item, ptr => by
      simp only [loadAt, loadAtWith]; exact ordinary_value _
    | .future item, ptr => by
      simp only [loadAt, loadAtWith]; exact ordinary_value _
    | .errorContext, ptr => by
      simp only [loadAt, loadAtWith]; exact ordinary_value _
  termination_by structural type => type

  theorem projectFields : ∀ (fields : List (String × WIT.ClosedType RtId)) (ptr : Nat),
      List.map Observed.value <$> loadFieldsAtWith limits cx width ownerCarrier fields ptr =
        loadFieldsAt limits quirks cx width fields ptr
    | [], _ => by simp only [loadFieldsAt, loadFieldsAtWith]; rfl
    | (_, item) :: fields, ptr => by
      simp only [loadFieldsAt, loadFieldsAtWith]
      exact projectBind Observed.value (List.map Observed.value) (project item _) fun _ =>
        projectBind (List.map Observed.value) (List.map Observed.value)
          (projectFields fields _) (fun _ => rfl)
  termination_by structural fields => fields

  theorem projectTypes : ∀ (types : List (WIT.ClosedType RtId)) (ptr : Nat),
      List.map Observed.value <$> loadTypesAtWith limits cx width ownerCarrier types ptr =
        loadTypesAt limits quirks cx width types ptr
    | [], _ => by simp only [loadTypesAt, loadTypesAtWith]; rfl
    | item :: types, ptr => by
      simp only [loadTypesAt, loadTypesAtWith]
      exact projectBind Observed.value (List.map Observed.value) (project item _) fun _ =>
        projectBind (List.map Observed.value) (List.map Observed.value)
          (projectTypes types _) (fun _ => rfl)
  termination_by structural types => types

  theorem projectCases : ∀ (cases : List (String × Option (WIT.ClosedType RtId))) (index ptr : Nat),
      Option.map Observed.value <$> loadCaseAtWith limits cx width ownerCarrier cases index ptr =
        loadCaseAt limits quirks cx width cases index ptr
    | [], _, _ => by simp only [loadCaseAt, loadCaseAtWith]; rfl
    | (_, item) :: _, 0, ptr => by
      simp only [loadCaseAt, loadCaseAtWith]; exact projectOptional item ptr
    | _ :: cases, index + 1, ptr => by
      simp only [loadCaseAt, loadCaseAtWith]; exact projectCases cases index ptr
  termination_by structural cases => cases

  theorem projectOptional : ∀ (item : Option (WIT.ClosedType RtId)) (ptr : Nat),
      Option.map Observed.value <$> loadOptAtWith limits cx width ownerCarrier item ptr =
        loadOptAt limits quirks cx width item ptr
    | none, _ => by simp only [loadOptAt, loadOptAtWith]; rfl
    | some item, ptr => by
      simp only [loadOptAt, loadOptAtWith]
      exact projectBind Observed.value (Option.map Observed.value) (project item ptr) (fun _ => rfl)
  termination_by structural item => item
end

local notation "flatOwner" => flatCarrier (World := World) limits quirks cx width
local notation "flatValue" => FlatLoadCarrier.reference (σ := World) limits quirks cx width
local notation "eraseValue" => Prod.map Observed.value (id : FlatCursor → FlatCursor)
local notation "eraseItems" => Prod.map (List.map Observed.value) (id : FlatCursor → FlatCursor)
local notation "eraseCase" => Prod.map (Option.map Observed.value) (id : FlatCursor → FlatCursor)

private theorem projectFlatN {left : FlatCursor → P E World (Observed × FlatCursor)}
    {right : FlatCursor → P E World (Val × FlatCursor)}
    (agree : ∀ cursor, eraseValue <$> left cursor = right cursor) (count : Nat)
    (cursor : FlatCursor) : eraseItems <$> liftFlatN left count cursor = liftFlatN right count cursor := by
  induction count generalizing cursor with
  | zero => rfl
  | succ count ih =>
    simp only [liftFlatN]
    exact projectBind eraseValue eraseItems (agree cursor) fun value =>
      projectBind eraseItems eraseItems (ih value.2) fun _ => rfl

private theorem projectFlatList (layout : Layout) {left : Nat → P E World Observed}
    {right : Nat → P E World Val} (agree : ∀ ptr, Observed.value <$> left ptr = right ptr)
    (cursor : FlatCursor) :
    eraseValue <$> liftFlatListUsing limits cx width layout (Observed.aggregate Val.list) left cursor =
      liftFlatListWith limits cx width layout right cursor := by
  unfold liftFlatListUsing liftFlatListWith
  exact fixedBind _ fun (ptr, _) => fixedBind _ fun (count, _) =>
    projectBind (List.map Observed.value) eraseValue
      (projectRange limits cx layout agree (flatNat ptr) (flatNat count)) fun _ => rfl

private theorem projectFlatVariant (count : Nat) (joined : List CoreType) (wants : Nat → List CoreType)
    {left : Nat → FlatCursor → P E World (Option Observed × FlatCursor)}
    {right : Nat → FlatCursor → P E World (Option Val × FlatCursor)}
    (agree : ∀ index cursor, eraseCase <$> left index cursor = right index cursor)
    (cursor : FlatCursor) :
    eraseValue <$> liftFlatVariantUsing count joined wants Observed.variant left cursor =
      liftFlatVariantWith count joined wants right cursor := by
  unfold liftFlatVariantUsing liftFlatVariantWith
  exact fixedBind _ fun (discr, _) => fixedBind _ fun _ => fixedBind _ fun _ =>
    projectBind eraseCase eraseValue (agree (flatNat discr) _) fun _ => rfl

mutual
  theorem projectFlat : ∀ (type : WIT.ClosedType RtId) (cursor : FlatCursor),
      eraseValue <$> liftFlatAtWith limits cx width flatOwner type cursor =
        liftFlatAt limits quirks cx width type cursor
    | .prim prim, cursor => by
      simp only [liftFlatAt, liftFlatAtWith, flatCarrier, Functor.map_map]
      exact id_map _
    | .ref impossible, _ => nomatch impossible
    | .list item, cursor => by
      simp only [liftFlatAt, liftFlatAtWith]
      exact projectFlatList limits cx width _ (project limits quirks cx width item) cursor
    | .fixedList item count, cursor => by
      simp only [liftFlatAt, liftFlatAtWith]
      exact projectBind eraseItems eraseValue
        (projectFlatN (projectFlat item) count cursor) fun _ => rfl
    | .record fields, cursor => by
      simp only [liftFlatAt, liftFlatAtWith]
      exact projectBind eraseItems eraseValue (projectFlatFields fields cursor) fun _ => rfl
    | .tuple items, cursor => by
      simp only [liftFlatAt, liftFlatAtWith]
      exact projectBind eraseItems eraseValue (projectFlatTypes items cursor) fun _ => rfl
    | .variant cases, cursor => by
      simp only [liftFlatAt, liftFlatAtWith]
      exact projectFlatVariant _ _ _ (projectFlatCases cases) cursor
    | .enum labels, cursor => by
      simp only [liftFlatAt, liftFlatAtWith]
      exact projectFlatVariant _ _ _ (fun _ _ => rfl) cursor
    | .flags labels, cursor => by
      simp only [liftFlatAt, liftFlatAtWith]
      exact fixedBind _ fun _ => rfl
    | .option item, cursor => by
      simp only [liftFlatAt, liftFlatAtWith]
      apply projectFlatVariant
      intro index cursor
      rcases index with _ | _ | _
      · rfl
      · exact projectBind eraseValue eraseCase (projectFlat item cursor) fun _ => rfl
      · rfl
    | .result ok err, cursor => by
      simp only [liftFlatAt, liftFlatAtWith]
      apply projectFlatVariant
      intro index cursor
      rcases index with _ | _ | _
      · exact projectFlatOption ok cursor
      · exact projectFlatOption err cursor
      · rfl
    | .map key item, cursor => by
      simp only [liftFlatAt, liftFlatAtWith]
      refine projectFlatList limits cx width _ ?_ cursor
      intro ptr
      unfold loadMapEntryUsing
      exact projectBind Observed.value Observed.value (ordinary_value _) fun _ =>
        projectBind Observed.value Observed.value (project limits quirks cx width item _) fun _ => rfl
    | .own resource, cursor => by
      simp only [liftFlatAt, liftFlatAtWith]
      exact fixedBind _ fun (slot, _) =>
        projectBind Observed.value eraseValue (own_value cx resource (flatNat slot)) fun _ => rfl
    | .borrow resource, cursor => by
      simp only [liftFlatAt, liftFlatAtWith]
      exact fixedBind _ fun _ => projectBind Observed.value eraseValue (ordinary_value _) fun _ => rfl
    | .stream item, cursor => by
      simp only [liftFlatAt, liftFlatAtWith]
      exact fixedBind _ fun _ => projectBind Observed.value eraseValue (ordinary_value _) fun _ => rfl
    | .future item, cursor => by
      simp only [liftFlatAt, liftFlatAtWith]
      exact fixedBind _ fun _ => projectBind Observed.value eraseValue (ordinary_value _) fun _ => rfl
    | .errorContext, cursor => by
      simp only [liftFlatAt, liftFlatAtWith]
      exact fixedBind _ fun _ => projectBind Observed.value eraseValue (ordinary_value _) fun _ => rfl
  termination_by structural type => type

  theorem projectFlatFields : ∀ (fields : List (String × WIT.ClosedType RtId)) (cursor : FlatCursor),
      eraseItems <$> liftFlatFieldsWith limits cx width flatOwner fields cursor =
        liftFlatFields limits quirks cx width fields cursor
    | [], _ => by simp only [liftFlatFields, liftFlatFieldsWith]; rfl
    | (_, item) :: fields, cursor => by
      simp only [liftFlatFields, liftFlatFieldsWith]
      exact projectBind eraseValue eraseItems (projectFlat item cursor) fun value =>
        projectBind eraseItems eraseItems (projectFlatFields fields value.2) fun _ => rfl
  termination_by structural fields => fields

  theorem projectFlatTypes : ∀ (items : List (WIT.ClosedType RtId)) (cursor : FlatCursor),
      eraseItems <$> liftFlatTypesWith limits cx width flatOwner items cursor =
        liftFlatTypes limits quirks cx width items cursor
    | [], _ => by simp only [liftFlatTypes, liftFlatTypesWith]; rfl
    | item :: items, cursor => by
      simp only [liftFlatTypes, liftFlatTypesWith]
      exact projectBind eraseValue eraseItems (projectFlat item cursor) fun value =>
        projectBind eraseItems eraseItems (projectFlatTypes items value.2) fun _ => rfl
  termination_by structural items => items

  theorem projectFlatCases : ∀ (cases : List (String × Option (WIT.ClosedType RtId)))
      (index : Nat) (cursor : FlatCursor),
      eraseCase <$> liftFlatCaseAtWith limits cx width flatOwner cases index cursor =
        liftFlatCaseAt limits quirks cx width cases index cursor
    | [], _, _ => by simp only [liftFlatCaseAt, liftFlatCaseAtWith]; rfl
    | (_, item) :: _, 0, cursor => by
      simp only [liftFlatCaseAt, liftFlatCaseAtWith]; exact projectFlatOption item cursor
    | _ :: cases, index + 1, cursor => by
      simp only [liftFlatCaseAt, liftFlatCaseAtWith]; exact projectFlatCases cases index cursor
  termination_by structural cases => cases

  theorem projectFlatOption : ∀ (item : Option (WIT.ClosedType RtId)) (cursor : FlatCursor),
      eraseCase <$> liftFlatOptWith limits cx width flatOwner item cursor =
        liftFlatOpt limits quirks cx width item cursor
    | none, _ => by simp only [liftFlatOpt, liftFlatOptWith]; rfl
    | some item, cursor => by
      simp only [liftFlatOpt, liftFlatOptWith]
      exact projectBind eraseValue eraseCase (projectFlat item cursor) fun _ => rfl
  termination_by structural item => item
end

theorem projectFlatValues (limits : Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (max : Nat) (cursor : FlatCursor) (types : List (WIT.ClosedType RtId)) :
    Prod.map (List.map Observed.value) id <$>
        liftFlatValuesWith limits cx (flatCarrier (World := World) limits quirks cx) max cursor types =
      liftFlatValues limits quirks cx max cursor types := by
  unfold liftFlatValues liftFlatValuesWith
  apply fixedBind
  intro width
  split
  · exact fixedBind _ fun (ptr, _) => fixedBind _ fun _ => fixedBind _ fun _ =>
      projectBind (List.map Observed.value) (Prod.map (List.map Observed.value) id)
        (projectTypes limits quirks cx width types (flatNat ptr)) fun _ => rfl
  · exact projectFlatTypes limits quirks cx width types cursor

theorem projectLowerOnStart (limits : Limits) (quirks : Quirks) (caller : CallerId) :
    List.map Observed.value <$> observeLowerOnStart (E := E) (World := World) limits quirks caller =
      lowerOnStart limits quirks caller := by
  unfold observeLowerOnStart lowerOnStart lowerOnStartWith
  apply fixedBind
  intro entry
  cases entry with
  | lower subtask cx args pos ft maxParams maxResults =>
    exact fixedBind _ fun _ => fixedBind _ fun _ =>
      projectBind (Prod.map (List.map Observed.value) id) (List.map Observed.value)
        (projectFlatValues limits quirks cx maxParams ⟨args, pos⟩ (ft.params.map (·.2)))
        fun (_, _) => fixedBind _ fun _ => rfl
  | host | sub =>
    change _ <$> (internal _ : P E World (List Observed)) = internal _
    unfold internal trap
    apply congrArg (Prog.op (S := Eff E World) (Op.trap _))
    exact funext fun impossible => nomatch impossible

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory
