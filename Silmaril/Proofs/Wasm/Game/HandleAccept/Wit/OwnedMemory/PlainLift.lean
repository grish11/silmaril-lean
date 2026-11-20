module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Plain.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Conservative

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.PlainLift

open Silmaril.Wasm (AddrType)
open Silmaril.Formats
open Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value
  Silmaril.Wasm.Game.HandleAccept.Wit Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory

variable {E : CoreEngine} {World : Type}

private theorem mapBind {α β γ δ : Type} (embedIn : α → β) (embedOut : γ → δ)
    {before : P E World α} {after : P E World β} {left : α → P E World γ}
    {right : β → P E World δ} (first : embedIn <$> before = after)
    (next : ∀ input, embedOut <$> left input = right (embedIn input)) :
    embedOut <$> (before >>= left) = after >>= right := by
  rw [map_bind, ← first, bind_map_left]
  exact congrArg (fun cont => before >>= cont) (funext next)

private theorem fixedBind {α β γ : Type} (embed : β → γ) {step : P E World α}
    {left : α → P E World β} {right : α → P E World γ}
    (next : ∀ input, embed <$> left input = right input) :
    embed <$> (step >>= left) = step >>= right := by
  rw [map_bind]
  exact congrArg (fun cont => step >>= cont) (funext next)

private theorem mapItems {α : Type} {left : α → P E World Val}
    {right : α → P E World Observed} (agree : ∀ input, Observed.ordinary <$> left input = right input)
    (inputs : List α) :
    List.map Observed.ordinary <$> Prog.mapM left inputs = Prog.mapM right inputs := by
  induction inputs with
  | nil => simp only [Prog.mapM_nil, ← Prog.pure_eq, map_pure, List.map_nil]
  | cons head tail ih =>
    simp only [Prog.mapM_cons]
    exact mapBind Observed.ordinary (List.map Observed.ordinary) (agree head) fun _ =>
      mapBind (List.map Observed.ordinary) (List.map Observed.ordinary) ih fun _ => rfl

private theorem mapRange (limits : Limits) (cx : LiftLowerContext E) (layout : Layout)
    {left : Nat → P E World Val} {right : Nat → P E World Observed}
    (agree : ∀ ptr, Observed.ordinary <$> left ptr = right ptr) (ptr count : Nat) :
    List.map Observed.ordinary <$> loadListFromRangeWith limits cx layout left ptr count =
      loadListFromRangeWith limits cx layout right ptr count := by
  unfold loadListFromRangeWith loadListFromValidRangeWith
  exact fixedBind _ fun _ => fixedBind _ fun _ => fixedBind _ fun _ =>
    mapItems (fun _ => agree _) _

private theorem mapList (limits : Limits) (cx : LiftLowerContext E) (width : AddrType)
    (layout : Layout) {left : Nat → P E World Val} {right : Nat → P E World Observed}
    (agree : ∀ ptr, Observed.ordinary <$> left ptr = right ptr) (ptr : Nat) :
    List.map Observed.ordinary <$> loadListWith limits cx width layout left ptr =
      loadListWith limits cx width layout right ptr := by
  unfold loadListWith
  exact fixedBind _ fun base => fixedBind _ fun len => mapRange limits cx layout agree base len

private theorem variant_map (index : Nat) (payload : Option Val) :
    Observed.ordinary (.variant index payload) =
      Observed.variant index (payload.map Observed.ordinary) := by
  cases payload <;> rfl

private theorem mapVariant (cx : LiftLowerContext E) (count : Nat) (alignment : Alignment)
    {left : Nat → Nat → P E World (Option Val)}
    {right : Nat → Nat → P E World (Option Observed)}
    (agree : ∀ index ptr, Option.map Observed.ordinary <$> left index ptr = right index ptr)
    (ptr : Nat) :
    Observed.ordinary <$> loadVariantWith cx count alignment left ptr =
      loadVariantUsing cx count alignment Observed.variant right ptr := by
  unfold loadVariantWith loadVariantUsing
  exact fixedBind _ fun discr => fixedBind _ fun _ =>
    mapBind (Option.map Observed.ordinary) Observed.ordinary (agree discr.toNat _) fun payload => by
      simp only [map_pure, variant_map]

private theorem aggregate_map (ctor : List Val → Val) (values : List Val) :
    Observed.aggregate ctor (values.map Observed.ordinary) = Observed.ordinary (ctor values) := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    simp only [Observed.aggregate, Observed.ordinary, List.map_cons, List.flatMap_cons,
      List.nil_append, List.map_map, Function.comp_def, List.map_id']
    exact congrArg (Observed.mk (ctor (head :: tail))) (congrArg Observed.owners ih)

variable (limits : Limits) (quirks : Quirks) (cx : LiftLowerContext E) (width : AddrType)

local notation "ownerCarrier" => carrier (World := World) limits quirks cx
local notation "readOwned" => loadAtWith limits cx width ownerCarrier
local notation "readVal" => loadAt (σ := World) limits quirks cx width

mutual
theorem load : ∀ (type : Stored.TypeOf) (ptr : Nat), Stored.payloadContainsOwn type = false →
    Observed.ordinary <$> readVal type ptr = readOwned type ptr
  | .ref impossible, _, _ => nomatch impossible
  | .own _, _, plain => nomatch plain
  | .prim _, _, _ | .flags _, _, _ | .borrow _, _, _ | .stream _, _, _ |
    .future _, _, _ | .errorContext, _, _ => by simp only [loadAt, loadAtWith]; rfl
  | .list item, ptr, plain => by
    simp only [loadAt, loadAtWith]
    exact mapBind (List.map Observed.ordinary) Observed.ordinary
      (mapList limits cx width _ (fun addr => load item addr plain) ptr) fun values => by
        simp only [carrier, LoadCarrier.reference, map_pure, aggregate_map]
  | .fixedList item count, ptr, plain => by
    simp only [loadAt, loadAtWith, loadListFromValidRangeWith]
    exact mapBind (List.map Observed.ordinary) Observed.ordinary
      (mapItems (fun _ => load item _ plain) (List.range count)) fun values => by
        simp only [carrier, LoadCarrier.reference, map_pure, aggregate_map]
  | .record fields, ptr, plain => by
    simp only [loadAt, loadAtWith]
    exact mapBind (List.map Observed.ordinary) Observed.ordinary
      (loadFields fields ptr plain) fun _ => by
        simp only [carrier, LoadCarrier.reference, map_pure, aggregate_map]
  | .tuple items, ptr, plain => by
    simp only [loadAt, loadAtWith]
    exact mapBind (List.map Observed.ordinary) Observed.ordinary
      (loadTypes items ptr plain) fun _ => by
        simp only [carrier, LoadCarrier.reference, map_pure, aggregate_map]
  | .variant cases, ptr, plain => by
    simp only [loadAt, loadAtWith]
    exact mapVariant cx _ _ (fun index addr => loadCases cases index addr plain) ptr
  | .enum _, ptr, _ => by
    simp only [loadAt, loadAtWith]
    exact mapVariant cx _ _ (fun _ _ => rfl) ptr
  | .option item, ptr, plain => by
    simp only [loadAt, loadAtWith]
    apply mapVariant
    intro index addr
    cases index with
    | zero => rfl
    | succ index =>
      cases index with
      | zero =>
        exact mapBind Observed.ordinary (Option.map Observed.ordinary)
          (load item addr plain) (fun _ => rfl)
      | succ _ => rfl
  | .result success failure, ptr, plain => by
    have both : Stored.payloadOptContainsOwn success = false ∧
        Stored.payloadOptContainsOwn failure = false := Bool.or_eq_false_iff.mp plain
    simp only [loadAt, loadAtWith]
    apply mapVariant
    intro index addr
    cases index with
    | zero => exact loadOptional success addr both.1
    | succ index =>
      cases index with
      | zero => exact loadOptional failure addr both.2
      | succ _ => rfl
  | .map key item, ptr, plain => by
    simp only [loadAt, loadAtWith]
    refine mapBind (List.map Observed.ordinary) Observed.ordinary
      (mapList limits cx width _ ?_ ptr) fun values => by
        simp only [carrier, LoadCarrier.reference, map_pure, aggregate_map]
    intro addr
    unfold loadMapEntryUsing
    exact mapBind Observed.ordinary Observed.ordinary rfl fun _ =>
      mapBind Observed.ordinary Observed.ordinary (load item _ plain) fun _ => rfl
termination_by structural type => type

theorem loadFields : ∀ (fields : List (String × Stored.TypeOf)) (ptr : Nat),
    Stored.payloadFieldsContainOwn fields = false →
    List.map Observed.ordinary <$> loadFieldsAt limits quirks cx width fields ptr =
      loadFieldsAtWith limits cx width ownerCarrier fields ptr
  | [], _, _ => by simp only [loadFieldsAt, loadFieldsAtWith]; rfl
  | (_, item) :: fields, ptr, plain => by
    have both : Stored.payloadContainsOwn item = false ∧
        Stored.payloadFieldsContainOwn fields = false := Bool.or_eq_false_iff.mp plain
    simp only [loadFieldsAt, loadFieldsAtWith]
    exact mapBind Observed.ordinary (List.map Observed.ordinary) (load item _ both.1) fun _ =>
      mapBind (List.map Observed.ordinary) (List.map Observed.ordinary)
        (loadFields fields _ both.2) (fun _ => rfl)
termination_by structural fields => fields

theorem loadTypes : ∀ (items : List Stored.TypeOf) (ptr : Nat),
    Stored.payloadTypesContainOwn items = false →
    List.map Observed.ordinary <$> loadTypesAt limits quirks cx width items ptr =
      loadTypesAtWith limits cx width ownerCarrier items ptr
  | [], _, _ => by simp only [loadTypesAt, loadTypesAtWith]; rfl
  | item :: items, ptr, plain => by
    have both : Stored.payloadContainsOwn item = false ∧
        Stored.payloadTypesContainOwn items = false := Bool.or_eq_false_iff.mp plain
    simp only [loadTypesAt, loadTypesAtWith]
    exact mapBind Observed.ordinary (List.map Observed.ordinary) (load item _ both.1) fun _ =>
      mapBind (List.map Observed.ordinary) (List.map Observed.ordinary)
        (loadTypes items _ both.2) (fun _ => rfl)
termination_by structural items => items

theorem loadCases : ∀ (cases : List (String × Option Stored.TypeOf)) (index ptr : Nat),
    Stored.payloadCasesContainOwn cases = false →
    Option.map Observed.ordinary <$> loadCaseAt limits quirks cx width cases index ptr =
      loadCaseAtWith limits cx width ownerCarrier cases index ptr
  | [], _, _, _ => by simp only [loadCaseAt, loadCaseAtWith]; rfl
  | (_, item) :: cases, index, ptr, plain => by
    have both : Stored.payloadOptContainsOwn item = false ∧
        Stored.payloadCasesContainOwn cases = false := Bool.or_eq_false_iff.mp plain
    cases index with
    | zero =>
      simp only [loadCaseAt, loadCaseAtWith]; exact loadOptional item ptr both.1
    | succ index =>
      simp only [loadCaseAt, loadCaseAtWith]; exact loadCases cases index ptr both.2
termination_by structural cases => cases

theorem loadOptional : ∀ (item : Option Stored.TypeOf) (ptr : Nat),
    Stored.payloadOptContainsOwn item = false →
    Option.map Observed.ordinary <$> loadOptAt limits quirks cx width item ptr =
      loadOptAtWith limits cx width ownerCarrier item ptr
  | none, _, _ => by simp only [loadOptAt, loadOptAtWith]; rfl
  | some item, ptr, plain => by
    simp only [loadOptAt, loadOptAtWith]
    exact mapBind Observed.ordinary (Option.map Observed.ordinary) (load item ptr plain) fun _ => rfl
termination_by structural item => item
end

local notation "flatOwner" => flatCarrier (World := World) limits quirks cx width
local notation "embedValue" => Prod.map Observed.ordinary (id : FlatCursor → FlatCursor)
local notation "embedItems" => Prod.map (List.map Observed.ordinary) (id : FlatCursor → FlatCursor)
local notation "embedCase" => Prod.map (Option.map Observed.ordinary) (id : FlatCursor → FlatCursor)

private theorem mapFlatN {left : FlatCursor → P E World (Val × FlatCursor)}
    {right : FlatCursor → P E World (Observed × FlatCursor)}
    (agree : ∀ cursor, embedValue <$> left cursor = right cursor) (count : Nat)
    (cursor : FlatCursor) : embedItems <$> liftFlatN left count cursor = liftFlatN right count cursor := by
  induction count generalizing cursor with
  | zero => rfl
  | succ count ih =>
    simp only [liftFlatN]
    exact mapBind embedValue embedItems (agree cursor) fun value =>
      mapBind embedItems embedItems (ih value.2) fun _ => rfl

private theorem mapFlatList (layout : Layout) {left : Nat → P E World Val}
    {right : Nat → P E World Observed} (agree : ∀ ptr, Observed.ordinary <$> left ptr = right ptr)
    (cursor : FlatCursor) :
    embedValue <$> liftFlatListWith limits cx width layout left cursor =
      liftFlatListUsing limits cx width layout (Observed.aggregate Val.list) right cursor := by
  unfold liftFlatListUsing liftFlatListWith
  exact fixedBind _ fun (ptr, _) => fixedBind _ fun (count, _) =>
    mapBind (List.map Observed.ordinary) embedValue
      (mapRange limits cx layout agree (flatNat ptr) (flatNat count)) fun _ => by
        simp only [map_pure, Prod.map_apply, id_eq, aggregate_map]

private theorem mapFlatVariant (count : Nat) (joined : List CoreType) (wants : Nat → List CoreType)
    {left : Nat → FlatCursor → P E World (Option Val × FlatCursor)}
    {right : Nat → FlatCursor → P E World (Option Observed × FlatCursor)}
    (agree : ∀ index cursor, embedCase <$> left index cursor = right index cursor)
    (cursor : FlatCursor) :
    embedValue <$> liftFlatVariantWith count joined wants left cursor =
      liftFlatVariantUsing count joined wants Observed.variant right cursor := by
  unfold liftFlatVariantUsing liftFlatVariantWith
  exact fixedBind _ fun (discr, _) => fixedBind _ fun _ => fixedBind _ fun _ =>
    mapBind embedCase embedValue (agree (flatNat discr) _) fun (payload, _) => by
      simp only [map_pure, Prod.map_apply, id_eq, variant_map]

mutual
theorem flat : ∀ (type : Stored.TypeOf) (cursor : FlatCursor), Stored.payloadContainsOwn type = false →
    embedValue <$> liftFlatAt limits quirks cx width type cursor =
      liftFlatAtWith limits cx width flatOwner type cursor
  | .ref impossible, _, _ => nomatch impossible
  | .own _, _, plain => nomatch plain
  | .prim _, _, _ => by simp only [liftFlatAt, liftFlatAtWith]; rfl
  | .list item, cursor, plain => by
    simp only [liftFlatAt, liftFlatAtWith]
    exact mapFlatList limits cx width _ (fun ptr => load limits quirks cx width item ptr plain) cursor
  | .fixedList item count, cursor, plain => by
    simp only [liftFlatAt, liftFlatAtWith]
    exact mapBind embedItems embedValue (mapFlatN (fun cur => flat item cur plain) count cursor)
      fun (_, _) => by simp only [flatCarrier, FlatLoadCarrier.reference, carrier,
        LoadCarrier.reference, map_pure, Prod.map_apply, id_eq, aggregate_map]
  | .record fields, cursor, plain => by
    simp only [liftFlatAt, liftFlatAtWith]
    exact mapBind embedItems embedValue (flatFields fields cursor plain)
      fun (_, _) => by simp only [flatCarrier, FlatLoadCarrier.reference, carrier,
        LoadCarrier.reference, map_pure, Prod.map_apply, id_eq, aggregate_map]
  | .tuple items, cursor, plain => by
    simp only [liftFlatAt, liftFlatAtWith]
    exact mapBind embedItems embedValue (flatTypes items cursor plain)
      fun (_, _) => by simp only [flatCarrier, FlatLoadCarrier.reference, carrier,
        LoadCarrier.reference, map_pure, Prod.map_apply, id_eq, aggregate_map]
  | .variant cases, cursor, plain => by
    simp only [liftFlatAt, liftFlatAtWith]
    exact mapFlatVariant _ _ _ (fun index cur => flatCases cases index cur plain) cursor
  | .enum _, cursor, _ => by
    simp only [liftFlatAt, liftFlatAtWith]
    exact mapFlatVariant _ _ _ (fun _ _ => rfl) cursor
  | .flags _, _, _ => by
    simp only [liftFlatAt, liftFlatAtWith]
    exact fixedBind _ fun _ => rfl
  | .option item, cursor, plain => by
    simp only [liftFlatAt, liftFlatAtWith]
    apply mapFlatVariant
    intro index cursor
    rcases index with _ | _ | _
    · rfl
    · exact mapBind embedValue embedCase (flat item cursor plain) fun _ => rfl
    · rfl
  | .result success failure, cursor, plain => by
    have both : Stored.payloadOptContainsOwn success = false ∧
        Stored.payloadOptContainsOwn failure = false := Bool.or_eq_false_iff.mp plain
    simp only [liftFlatAt, liftFlatAtWith]
    apply mapFlatVariant
    intro index cursor
    rcases index with _ | _ | _
    · exact flatOptional success cursor both.1
    · exact flatOptional failure cursor both.2
    · rfl
  | .map key item, cursor, plain => by
    simp only [liftFlatAt, liftFlatAtWith]
    refine mapFlatList limits cx width _ ?_ cursor
    intro ptr
    unfold loadMapEntryUsing
    exact mapBind Observed.ordinary Observed.ordinary rfl fun _ =>
      mapBind Observed.ordinary Observed.ordinary (load limits quirks cx width item _ plain) fun _ => rfl
  | .borrow _, _, _ | .stream _, _, _ | .future _, _, _ | .errorContext, _, _ => by
    simp only [liftFlatAt, liftFlatAtWith]
    exact fixedBind _ fun _ => mapBind Observed.ordinary embedValue rfl fun _ => rfl
termination_by structural type => type

theorem flatFields : ∀ (fields : List (String × Stored.TypeOf)) (cursor : FlatCursor),
    Stored.payloadFieldsContainOwn fields = false →
    embedItems <$> liftFlatFields limits quirks cx width fields cursor =
      liftFlatFieldsWith limits cx width flatOwner fields cursor
  | [], _, _ => by simp only [liftFlatFields, liftFlatFieldsWith]; rfl
  | (_, item) :: fields, cursor, plain => by
    have both : Stored.payloadContainsOwn item = false ∧
        Stored.payloadFieldsContainOwn fields = false := Bool.or_eq_false_iff.mp plain
    simp only [liftFlatFields, liftFlatFieldsWith]
    exact mapBind embedValue embedItems (flat item cursor both.1) fun value =>
      mapBind embedItems embedItems (flatFields fields value.2 both.2) fun _ => rfl
termination_by structural fields => fields

theorem flatTypes : ∀ (items : List Stored.TypeOf) (cursor : FlatCursor),
    Stored.payloadTypesContainOwn items = false →
    embedItems <$> liftFlatTypes limits quirks cx width items cursor =
      liftFlatTypesWith limits cx width flatOwner items cursor
  | [], _, _ => by simp only [liftFlatTypes, liftFlatTypesWith]; rfl
  | item :: items, cursor, plain => by
    have both : Stored.payloadContainsOwn item = false ∧
        Stored.payloadTypesContainOwn items = false := Bool.or_eq_false_iff.mp plain
    simp only [liftFlatTypes, liftFlatTypesWith]
    exact mapBind embedValue embedItems (flat item cursor both.1) fun value =>
      mapBind embedItems embedItems (flatTypes items value.2 both.2) fun _ => rfl
termination_by structural items => items

theorem flatCases : ∀ (cases : List (String × Option Stored.TypeOf)) (index : Nat) (cursor : FlatCursor),
    Stored.payloadCasesContainOwn cases = false →
    embedCase <$> liftFlatCaseAt limits quirks cx width cases index cursor =
      liftFlatCaseAtWith limits cx width flatOwner cases index cursor
  | [], _, _, _ => by simp only [liftFlatCaseAt, liftFlatCaseAtWith]; rfl
  | (_, item) :: cases, index, cursor, plain => by
    have both : Stored.payloadOptContainsOwn item = false ∧
        Stored.payloadCasesContainOwn cases = false := Bool.or_eq_false_iff.mp plain
    cases index with
    | zero =>
      simp only [liftFlatCaseAt, liftFlatCaseAtWith]; exact flatOptional item cursor both.1
    | succ index =>
      simp only [liftFlatCaseAt, liftFlatCaseAtWith]; exact flatCases cases index cursor both.2
termination_by structural cases => cases

theorem flatOptional : ∀ (item : Option Stored.TypeOf) (cursor : FlatCursor),
    Stored.payloadOptContainsOwn item = false →
    embedCase <$> liftFlatOpt limits quirks cx width item cursor =
      liftFlatOptWith limits cx width flatOwner item cursor
  | none, _, _ => by simp only [liftFlatOpt, liftFlatOptWith]; rfl
  | some item, cursor, plain => by
    simp only [liftFlatOpt, liftFlatOptWith]
    exact mapBind embedValue embedCase (flat item cursor plain) fun _ => rfl
termination_by structural item => item
end

theorem flatValues (limits : Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (max : Nat) (cursor : FlatCursor) (types : List Stored.TypeOf)
    (plain : Stored.payloadTypesContainOwn types = false) :
    embedItems <$> liftFlatValues limits quirks cx max cursor types =
      liftFlatValuesWith limits cx (flatCarrier (World := World) limits quirks cx) max cursor types := by
  unfold liftFlatValues liftFlatValuesWith
  apply fixedBind
  intro width
  split
  · exact fixedBind _ fun (ptr, _) => fixedBind _ fun _ => fixedBind _ fun _ =>
      mapBind (List.map Observed.ordinary) embedItems
        (loadTypes limits quirks cx width types (flatNat ptr) plain) fun _ => rfl
  · exact flatTypes limits quirks cx width types cursor plain

theorem liftPlain (limits : Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    {type : Stored.TypeOf} (admitted : Stored.checkSchema type = .ok ()) (input : Stored.Input) :
    lift (World := World) limits quirks cx type input =
      (fun result => (result.map (Payload.equivPlain admitted)).mapError Issue.schema) <$>
        Stored.lift limits quirks cx type input := by
  have checks : checkSchema type = .ok () ∧ Stored.payloadContainsOwn type = false := by
    unfold Stored.checkSchema at admitted
    split at admitted
    · cases admitted
    · rename_i notBorrow
      split at admitted
      · cases admitted
      · rename_i notOwn
        exact ⟨by unfold checkSchema; rw [ite_eq_right notBorrow]; exact admitted,
          Bool.eq_false_of_not_eq_true notOwn⟩
  unfold lift Stored.lift
  rw [checks.1, admitted]
  symm
  apply fixedBind
  intro width
  cases input with
  | memory ptr =>
    exact fixedBind _ fun _ => fixedBind _ fun _ =>
      mapBind Observed.ordinary _ (load limits quirks cx width type ptr checks.2) fun value => by
        rw [map_pure, checkValue_plain admitted value]
  | flat values =>
    dsimp only
    by_cases bad : (values.map Stored.flatType != flatten width type) = true
    · simp only [bad, ite_true, map_pure]; rfl
    · rw [ite_eq_right bad, ite_eq_right bad]
      exact mapBind embedValue _
        (flat limits quirks cx width type (FlatCursor.ofList values) checks.2) fun (value, _) => by
          rw [map_pure]
          exact congrArg pure (checkValue_plain admitted value).symm

private theorem embedNode (sig : PlainSignature) (tag : sig.val.Tag)
    (payload : Stored.Payload (sig.val.payload tag)) (children : List (Stored.Tree sig.val)) :
    Tree.equivPlain sig (AST.node tag payload children) =
      AST.node tag (Payload.equivPlain (sig.property tag) payload) (children.map (Tree.equivPlain sig)) := by
  apply (Tree.equivPlain sig).symm.injective
  rw [Equiv.symm_apply_apply, Tree.equivPlain_symm, Conservative.erase_node]
  simp only [← Tree.equivPlain_symm sig, List.map_map, Function.comp_def, Equiv.symm_apply_apply,
    List.map_id']
  have erasePayload := (Payload.equivPlain (sig.property tag)).symm_apply_apply payload
  rw [Payload.equivPlain_symm] at erasePayload
  rw [erasePayload]

theorem nodePlain (sig : PlainSignature) (limits : Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (tag : sig.val.Tag) (input : Stored.Input)
    (children : List (Stored.Tree sig.val)) :
    buildNode (World := World) sig.val limits quirks cx tag input (children.map (Tree.equivPlain sig)) =
      (fun result => (result.map (Tree.equivPlain sig)).mapError Issue.schema) <$>
        Stored.buildNode sig.val limits quirks cx tag input children := by
  unfold buildNode Stored.buildNode
  rw [List.length_map]
  split
  · simp only [map_pure]; rfl
  · rw [liftPlain limits quirks cx (sig.property tag) input]
    simp only [bind_map_left, map_bind, map_pure]
    congr 1
    funext result
    cases result <;> simp only [Except.map, Except.mapError, embedNode]

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.PlainLift
