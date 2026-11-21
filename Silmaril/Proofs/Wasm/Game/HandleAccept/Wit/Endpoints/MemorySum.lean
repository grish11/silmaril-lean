module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.MemorySum

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (TypeOf)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Lower (Output)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower.Internal (runField)

variable {E : CoreEngine} {World : Type}

private def armStore (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (ptr : Nat) : Option Field → P E World Unit
  | none => pure ()
  | some field => store limits quirks cx field.value field.type ptr

private theorem rejoin (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (authority : Authority E World) (width : AddrType) (type : TypeOf) (arms : List (Option TypeOf))
    (tag index ptr : Nat) (arm : Option Field)
    (child : ∀ field address, arm = some field →
      runField limits quirks cx authority width field 0 (.memory address) =
        Except.ok <$> store limits quirks cx field.value field.type address) :
    runField limits quirks cx authority width (.sum type arms tag arm) index (.memory ptr) =
      (do
        let address ← storeVariantHead cx arms.length (maxCaseAlignment (arms.map (layoutOption width))) tag ptr
        Except.ok <$> armStore limits quirks cx address arm) := by
  cases arm with
  | none =>
    simp [runField, armStore]
    rfl
  | some field =>
    rw [runField]
    dsimp only [Output.Result]
    simp only [armStore, child _ _ rfl, ← bind_pure_comp, Prog.bind_eq, Prog.bind_assoc]
    congr 1

private theorem caseStore_at (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (ptr : Nat) (payload : Option Val) (cases : List (String × Option TypeOf)) (tag : Nat)
    (selected : Option TypeOf) (found : (cases.map Prod.snd)[tag]? = some selected) :
    (storeCase limits quirks cx tag payload cases ptr : P E World _) =
      storeOpt limits quirks cx payload selected ptr := by
  induction cases generalizing tag with
  | nil => simp at found
  | cons entry rest ih =>
    cases tag with
    | zero =>
      have eq : entry.2 = selected := by simpa using found
      cases entry
      simpa [storeCase] using congrArg (fun t => storeOpt limits quirks cx payload t ptr) eq
    | succ tag =>
      rw [storeCase]
      exact ih tag (by simpa using found)

private theorem caseLayouts (width : AddrType) (cases : List (String × Option TypeOf)) :
    (cases.map Prod.snd).map (layoutOption width) = layoutCases width cases := by
  induction cases with
  | nil => simp [layoutCases]
  | cons entry rest ih =>
    cases entry
    simp [layoutCases, ih]

private theorem armStore_matches (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (ptr : Nat) {arm : Option Field} {type : Option TypeOf} (certificate : Field.ArmMatches arm type) :
    (armStore limits quirks cx ptr arm : P E World _) =
      storeOpt limits quirks cx (Field.armValue arm) type ptr := by
  cases certificate with
  | none => simp [armStore, storeOpt]
  | some layout => simp [armStore, storeOpt, Field.armValue, layout.type_eq]

private theorem sum_program_aux (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (type : TypeOf) (arms : List (Option TypeOf)) (tag ptr : Nat)
    (arm : Option Field) (layout : Field.LayoutMatches (.sum type arms tag arm) type) :
    (store limits quirks cx (.variant tag (Field.armValue arm)) type ptr : P E World _) = (do
      let width ← ptrType cx
      let address ← storeVariantHead cx arms.length (maxCaseAlignment (arms.map (layoutOption width))) tag ptr
      armStore limits quirks cx address arm) := by
  cases layout with
  | variant found certificate =>
    rw [store]
    congr 1
    funext width
    simp only [List.length_map, caseLayouts, caseStore_at _ _ _ _ _ _ _ _ found,
      armStore_matches _ _ _ _ certificate]
  | optionNone =>
    rw [store]
    congr 1
    funext width
    simp [armStore, layoutOption]
  | optionSome certificate =>
    rw [Field.armValue, store]
    congr 1
    funext width
    simp [armStore, layoutOption, certificate.type_eq]
  | resultOk certificate =>
    rw [store]
    congr 1
    funext width
    simp [armStore_matches _ _ _ _ certificate]
  | resultError certificate =>
    rw [store]
    congr 1
    funext width
    simp [armStore_matches _ _ _ _ certificate]

theorem sum_program (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (type : TypeOf) (arms : List (Option TypeOf)) (tag ptr : Nat)
    (arm : Option Field) (layout : Field.LayoutMatches (.sum type arms tag arm) type) :
    (store limits quirks cx (.variant tag (Field.armValue arm)) type ptr : P E World _) = (do
      let width ← ptrType cx
      let address ← storeVariantHead cx arms.length (maxCaseAlignment (arms.map (layoutOption width))) tag ptr
      match arm with
      | none => pure ()
      | some field => store limits quirks cx field.value field.type address) :=
  sum_program_aux limits quirks cx type arms tag ptr arm layout

theorem sum_rejoin (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (authority : Authority E World) (type : TypeOf) (arms : List (Option TypeOf)) (tag index ptr : Nat)
    (arm : Option Field) (layout : Field.LayoutMatches (.sum type arms tag arm) type)
    (child : ∀ width field address, arm = some field →
      runField limits quirks cx authority width field 0 (.memory address) =
        Except.ok <$> store limits quirks cx field.value field.type address) :
    (do
      let width ← ptrType cx
      runField limits quirks cx authority width (.sum type arms tag arm) index (.memory ptr)) =
      Except.ok <$> store limits quirks cx (.variant tag (Field.armValue arm)) type ptr := by
  rw [sum_program_aux limits quirks cx type arms tag ptr arm layout]
  dsimp only [Output.Result]
  simp only [← bind_pure_comp, Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext width
  rw [rejoin limits quirks cx authority width type arms tag index ptr arm (child width)]
  dsimp only [Output.Result]
  simp only [← bind_pure_comp, Prog.bind_eq]

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.MemorySum
