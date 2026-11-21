module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.FlatSum

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (TypeOf)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Lower (Output)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower.Internal (runField)

variable {E : CoreEngine} {World : Type}

private def armTypes (width : AddrType) : Option Field → List CoreType
  | none => []
  | some field => flatten width field.type

private def armProgram (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (width : AddrType) : Option Field → P E World (List FlatValue)
  | none => pure []
  | some field => lowerFlatAt limits quirks cx width field.value field.type

private theorem rejoin (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (authority : Authority E World) (width : AddrType) (type : TypeOf) (arms : List (Option TypeOf))
    (tag index : Nat) (arm : Option Field) (valid : tag < arms.length)
    (child : ∀ field, arm = some field → runField limits quirks cx authority width field 0 .flat =
      Except.ok <$> lowerFlatAt limits quirks cx width field.value field.type) :
    runField limits quirks cx authority width (.sum type arms tag arm) index .flat =
      Except.ok <$> lowerFlatVariantWith arms.length ((flatten width type).drop 1) tag
        (armTypes width arm) (armProgram limits quirks cx width arm) := by
  cases arm with
  | none => rfl
  | some field =>
    rw [runField, child field rfl]
    dsimp only [Output.Result]
    simp only [armTypes, armProgram, lowerFlatVariantWith, ite_eq_left valid, ← bind_pure_comp,
      Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind']

private theorem lowerCase_at (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (width : AddrType) (payload : Option Val) (cases : List (String × Option TypeOf)) (tag : Nat)
    (selected : Option TypeOf) (found : (cases.map Prod.snd)[tag]? = some selected) :
    (lowerFlatCase limits quirks cx width tag payload cases : P E World _) =
      lowerFlatOpt limits quirks cx width payload selected := by
  induction cases generalizing tag with
  | nil => simp at found
  | cons entry rest ih =>
    cases tag with
    | zero =>
      have eq : entry.2 = selected := by simpa using found
      cases entry
      simpa [lowerFlatCase] using congrArg (lowerFlatOpt limits quirks cx width payload) eq
    | succ tag =>
      rw [lowerFlatCase]
      exact ih tag (by simpa using found)

private theorem caseTypes_at (width : AddrType) (cases : List (String × Option TypeOf)) (tag : Nat)
    (selected : Option TypeOf) (found : (cases.map Prod.snd)[tag]? = some selected) :
    caseFlat width cases tag = flattenOption width selected := by
  rw [List.getElem?_map] at found
  cases atTag : cases[tag]? with
  | none => simp [atTag] at found
  | some entry =>
    have eq : entry.2 = selected := by simpa [atTag] using found
    cases entry
    simpa [caseFlat, atTag] using congrArg (flattenOption width) eq

private theorem armTypes_match (width : AddrType) {arm : Option Field} {type : Option TypeOf}
    (certificate : Field.ArmMatches arm type) : armTypes width arm = flattenOption width type := by
  cases certificate with
  | none => simp [armTypes, flattenOption]
  | some layout => simp [armTypes, flattenOption, layout.type_eq]

private theorem armProgram_matches (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (width : AddrType) {arm : Option Field} {type : Option TypeOf} (certificate : Field.ArmMatches arm type) :
    (armProgram limits quirks cx width arm : P E World _) =
      lowerFlatOpt limits quirks cx width (Field.armValue arm) type := by
  cases certificate with
  | none => simp [armProgram, lowerFlatOpt]
  | some layout => simp [armProgram, lowerFlatOpt, Field.armValue, layout.type_eq]

private theorem sum_program_aux (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (width : AddrType) (type : TypeOf) (arms : List (Option TypeOf))
    (tag : Nat) (arm : Option Field) (layout : Field.LayoutMatches (.sum type arms tag arm) type) :
    (lowerFlatAt limits quirks cx width (.variant tag (Field.armValue arm)) type : P E World _) =
      lowerFlatVariantWith arms.length ((flatten width type).drop 1) tag
        (armTypes width arm) (armProgram limits quirks cx width arm) := by
  cases layout with
  | variant found certificate =>
    rw [lowerFlatAt, caseTypes_at _ _ _ _ found, lowerCase_at _ _ _ _ _ _ _ _ found,
      armTypes_match _ certificate, armProgram_matches _ _ _ _ certificate]
    simp [flatten]
  | optionNone =>
    simp [Field.armValue, lowerFlatAt, flatten, armTypes, armProgram, optionWants]
  | optionSome layout =>
    simp [Field.armValue, lowerFlatAt, flatten, armTypes, armProgram, optionWants, layout.type_eq]
  | resultOk certificate =>
    rw [lowerFlatAt, armTypes_match _ certificate, armProgram_matches _ _ _ _ certificate]
    simp [flatten, resultWants]
  | resultError certificate =>
    rw [lowerFlatAt, armTypes_match _ certificate, armProgram_matches _ _ _ _ certificate]
    simp [flatten, resultWants]

theorem sum_program (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (width : AddrType) (type : TypeOf) (arms : List (Option TypeOf))
    (tag : Nat) (arm : Option Field) (layout : Field.LayoutMatches (.sum type arms tag arm) type) :
    (lowerFlatAt limits quirks cx width (.variant tag (Field.armValue arm)) type : P E World _) =
      lowerFlatVariantWith arms.length ((flatten width type).drop 1) tag
        (match arm with | none => [] | some field => flatten width field.type)
        (match arm with | none => pure [] | some field => lowerFlatAt limits quirks cx width field.value field.type) :=
  by cases arm <;> exact sum_program_aux limits quirks cx width type arms tag _ layout

theorem sum_rejoin (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (authority : Authority E World) (width : AddrType) (type : TypeOf) (arms : List (Option TypeOf))
    (tag index : Nat) (arm : Option Field) (layout : Field.LayoutMatches (.sum type arms tag arm) type)
    (child : ∀ field, arm = some field → runField limits quirks cx authority width field 0 .flat =
      Except.ok <$> lowerFlatAt limits quirks cx width field.value field.type) :
    runField limits quirks cx authority width (.sum type arms tag arm) index .flat =
      Except.ok <$> lowerFlatAt limits quirks cx width (.variant tag (Field.armValue arm)) type := by
  rw [sum_program_aux limits quirks cx width type arms tag arm layout]
  apply rejoin limits quirks cx authority width type arms tag index arm _ child
  cases layout with
  | variant found certificate => exact List.getElem?_eq_some_iff.mp found |>.1
  | _ => simp

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.FlatSum
