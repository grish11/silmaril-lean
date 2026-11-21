module

public import Silmaril.Wasm.Validation.Intrinsic.Defs
import Silmaril.Wasm.ModuleParts.Thms

@[expose] public section

namespace Silmaril.Proofs.Wasm.Validation.Intrinsic

open Silmaril.Wasm Silmaril.Wasm.Validation
open Silmaril.Wasm.Validation.Intrinsic (Step Body Function Functions)

mutual

theorem step_sound {context sig} : (step : Step context sig) → InstrOk context step.erase sig
  | .atom _ _ typed => typed
  | .localGet ref => .variable (.localGet ref.resolves)
  | .localSet ref => .variable (.localSet ref.resolves)
  | .localTee ref => .variable (.localTee ref.resolves)
  | .call ref => .call ref.ref.resolves ref.expands
  | .br ref stack => .br ref.resolves stack
  | .brIf ref => .brIf ref.resolves
  | .return_ ref stack => .return_ ref stack
  | .unreachable stack => .parametric (.unreachable stack)
  | .block _ valid body => .block valid (body_sound body)
  | .loop _ valid body => .loop valid (body_sound body)
  | .if_ _ valid yes no => .if_ valid (body_sound yes) (body_sound no)
  | .tryTable _ valid _ catches body => .tryTable valid (body_sound body) catches

theorem body_sound {context sig} : (body : Body context sig) → InstrsOk context body.erase sig
  | .nil => .nil
  | .single step => .instr (step_sound step)
  | .seq first locals rest => .seq (body_sound first) locals (body_sound rest)
  | .sub body subtype valid => .sub (body_sound body) subtype valid
  | .frame body valid => .frame (body_sound body) valid

end

private theorem lift_atom {context op sig} (typed : InstrOk context op sig)
    (atomic : Validation.Intrinsic.isAtomic op = true) :
    ∃ step : Step context sig, step.erase = op := ⟨.atom op atomic typed, rfl⟩

theorem lift_body {context ops sig} (typed : InstrsOk context ops sig) :
    ∃ body : Body context sig, body.erase = ops := by
  apply InstrsOk.rec (motive_1 := fun ctx op effect _ => ∃ step : Step ctx effect, step.erase = op)
    (motive_2 := fun ctx instrs effect _ => ∃ body : Body ctx effect, body.erase = instrs) (t := typed)
  case parametric =>
    intro _ _ _ valid
    cases valid with
    | unreachable stack => exact ⟨.unreachable stack, rfl⟩
    | nop => exact ⟨.atom _ rfl (.parametric .nop), rfl⟩
    | drop valid => exact ⟨.atom _ rfl (.parametric (.drop valid)), rfl⟩
    | selectExpl valid => exact ⟨.atom _ rfl (.parametric (.selectExpl valid)), rfl⟩
    | selectImpl valid sub numeric => exact ⟨.atom _ rfl (.parametric (.selectImpl valid sub numeric)), rfl⟩
  case «variable» =>
    intro _ _ _ valid
    cases valid with
    | localGet lookup => exact ⟨.localGet ⟨_, lookup⟩, rfl⟩
    | localSet lookup => exact ⟨.localSet ⟨_, lookup⟩, rfl⟩
    | localTee lookup => exact ⟨.localTee ⟨_, lookup⟩, rfl⟩
    | globalGet lookup => exact ⟨.atom _ rfl (.variable (.globalGet lookup)), rfl⟩
    | globalSet lookup => exact ⟨.atom _ rfl (.variable (.globalSet lookup)), rfl⟩
  case block =>
    intro _ blockType _ _ _ _ valid _ ih
    obtain ⟨body, rfl⟩ := ih
    exact ⟨.block blockType valid body, rfl⟩
  case loop =>
    intro _ blockType _ _ _ _ valid _ ih
    obtain ⟨body, rfl⟩ := ih
    exact ⟨.loop blockType valid body, rfl⟩
  case if_ =>
    intro _ blockType _ _ _ _ _ _ valid _ _ ihYes ihNo
    obtain ⟨yes, rfl⟩ := ihYes
    obtain ⟨no, rfl⟩ := ihNo
    exact ⟨.if_ blockType valid yes no, rfl⟩
  case tryTable =>
    intro _ blockType catches _ _ _ _ valid _ validCatches ih
    obtain ⟨body, rfl⟩ := ih
    exact ⟨.tryTable blockType valid catches validCatches body, rfl⟩
  case call =>
    intro _ index type _ _ lookup expands
    exact ⟨.call ⟨type, ⟨index, lookup⟩, expands⟩, rfl⟩
  case br =>
    intro _ index _ _ _ lookup stack
    exact ⟨.br ⟨index, lookup⟩ stack, rfl⟩
  case brIf =>
    intro _ index _ lookup
    exact ⟨.brIf ⟨index, lookup⟩, rfl⟩
  case return_ =>
    intro _ _ _ _ lookup stack
    exact ⟨.return_ lookup stack, rfl⟩
  case nil =>
    intro context
    exact ⟨.nil, rfl⟩
  case instr =>
    intro _ _ _ _ ih
    obtain ⟨step, rfl⟩ := ih
    exact ⟨.single step, rfl⟩
  case seq =>
    intro _ _ _ _ _ _ _ _ _ locals _ ihFirst ihRest
    obtain ⟨first, rfl⟩ := ihFirst
    obtain ⟨rest, rfl⟩ := ihRest
    exact ⟨.seq first locals rest, rfl⟩
  case cons =>
    intro _ _ _ _ _ _ _ _ _ locals _ ihFirst ihRest
    obtain ⟨first, rfl⟩ := ihFirst
    obtain ⟨rest, rfl⟩ := ihRest
    exact ⟨.seq (.single first) locals rest, rfl⟩
  case sub =>
    intro _ _ _ _ _ subtype valid ih
    obtain ⟨body, rfl⟩ := ih
    exact ⟨.sub body subtype valid, rfl⟩
  case frame =>
    intro _ _ _ _ _ _ _ valid ih
    obtain ⟨body, rfl⟩ := ih
    exact ⟨.frame body valid, rfl⟩
  case numeric =>
    intro _ _ _ valid
    exact lift_atom (.numeric valid) (by cases valid <;> rfl)
  case vector =>
    intro _ _ _ valid
    exact lift_atom (.vector valid) (by cases valid <;> rfl)
  case memory =>
    intro _ _ _ valid
    exact lift_atom (.memory valid) (by cases valid <;> rfl)
  case table =>
    intro _ _ _ valid
    exact lift_atom (.table valid) (by cases valid <;> rfl)
  case reference =>
    intro _ _ _ valid
    exact lift_atom (.reference valid) (by cases valid <;> rfl)
  all_goals intros
  all_goals first
    | exact lift_atom (.brTable ‹_› ‹_› ‹_›) rfl
    | exact lift_atom (.brOnNull ‹_› ‹_›) rfl
    | exact lift_atom (.brOnNonNull ‹_›) rfl
    | exact lift_atom (.brOnCast ‹_› ‹_› ‹_› ‹_› ‹_›) rfl
    | exact lift_atom (.brOnCastFail ‹_› ‹_› ‹_› ‹_› ‹_›) rfl
    | exact lift_atom (.callRef ‹_› ‹_›) rfl
    | exact lift_atom (.callIndirect ‹_› ‹_› ‹_› ‹_›) rfl
    | exact lift_atom (.returnCall ‹_› ‹_› ‹_› ‹_› ‹_›) rfl
    | exact lift_atom (.returnCallRef ‹_› ‹_› ‹_› ‹_› ‹_›) rfl
    | exact lift_atom (.returnCallIndirect ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›) rfl
    | exact lift_atom (.throw ‹_› ‹_› ‹_›) rfl
    | exact lift_atom (.throwRef ‹_›) rfl

theorem function_sound {context type} (func : Function context type) : FuncOk context func.erase type :=
  .mk func.resolves func.expands func.localValid (body_sound func.body)

theorem lift_function {context raw type} (typed : FuncOk context raw type) :
    ∃ func : Function context type, func.erase = raw := by
  cases raw with
  | mk typeIndex locals ops =>
    cases typed with
    | mk lookup expands localValid bodyValid =>
      obtain ⟨body, he⟩ := lift_body bodyValid
      exact ⟨⟨typeIndex, lookup, _, _, expands, locals, _, localValid, body⟩, congrArg _ he⟩

theorem functions_sound {context types} (funcs : Functions context types) :
    List.Forall₂ (FuncOk context) funcs.erase types := by
  induction funcs with
  | nil => exact .nil
  | cons head _ ih => exact .cons (function_sound head) ih

theorem lift_functions {context raw types} (typed : List.Forall₂ (FuncOk context) raw types) :
    ∃ funcs : Functions context types, funcs.erase = raw := by
  induction typed with
  | nil => exact ⟨.nil, rfl⟩
  | cons typed _ ih =>
    obtain ⟨head, rfl⟩ := lift_function typed
    obtain ⟨tail, rfl⟩ := ih
    exact ⟨.cons head tail, rfl⟩

theorem module_sound {interface} (mod : Validation.Intrinsic.Module interface) :
    ModuleOk mod.erase interface := by
  cases interface
  exact .mk mod.typesValid mod.importsValid mod.baseContextEq mod.contextEq mod.tagsValid
    mod.globalsValid mod.memoriesValid mod.tablesValid (functions_sound mod.funcs) mod.dataValid
    mod.elemsValid mod.startValid mod.exportsValid mod.exportsDisjoint

theorem lift_module {raw interface} (typed : ModuleOk raw interface) :
    ∃ mod : Validation.Intrinsic.Module interface, mod.erase = raw := by
  cases typed with
  | mk types imports baseCtx ctx tags globals mems tables funcs data elems start exports disjoint =>
    obtain ⟨bodies, erased⟩ := lift_functions funcs
    refine ⟨{
      sections := raw.sections
      definedTypes := _
      definedTags := _
      definedGlobals := _
      definedTables := _
      definedFuncs := _
      elementTypes := _
      baseContext := _
      context := _
      typesValid := types
      importsValid := imports
      baseContextEq := baseCtx
      contextEq := ctx
      tagsValid := tags
      globalsValid := globals
      memoriesValid := mems
      tablesValid := tables
      funcs := bodies
      dataValid := data
      elemsValid := elems
      startValid := start
      exportsValid := exports
      exportsDisjoint := disjoint }, ?_⟩
    dsimp [Validation.Intrinsic.Module.erase]
    rw [erased]
    exact raw.assemble_sections

end Silmaril.Proofs.Wasm.Validation.Intrinsic
