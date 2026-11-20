module

public import Silmaril.Wasm.Validation.Intrinsic.Defs
public import Silmaril.Wasm.Validation.Check.Validate

@[expose] public section

namespace Silmaril.Wasm.Validation.Intrinsic.Reify

abbrev ExactStep (context : Context) (op : Instr) :=
  Σ input output : List CValType, { step : Step context (.plain input output) // step.erase = op }

def step? (context : Context) (stack : List CValType) (op : Instr) : Option (ExactStep context op) :=
  match op with
  | .localGet index => do
    let ⟨⟨.set, type⟩, resolves⟩ ← context.locals[index.toNat]?.attach | none
    some ⟨[], [type], .localGet ⟨index, resolves⟩, rfl⟩
  | .call index => do
    let ⟨type, resolves⟩ ← context.funcs[index.toNat]?.attach
    let ⟨.func params results, expands⟩ ← type.expand?.attach | none
    some ⟨params.toList, results.toList, .call ⟨type, ⟨index, resolves⟩, Expand.iff.mpr expands⟩, rfl⟩
  | .nop => some ⟨[], [], .atom .nop rfl (.parametric .nop), rfl⟩
  | .drop => do
    let type ← stack.getLast?
    if valid : TyOk.check context.toTypeCtx type = true then
      some ⟨[type], [], .atom .drop rfl (.parametric (.drop (TyOk.check_sound valid))), rfl⟩
    else none
  | op => do
    let ⟨⟨input, [], output⟩, typed⟩ ← (numericType? op).attach | none
    if atomic : isAtomic op = true then
      some ⟨input, output, .atom op atomic (.numeric (numericType?_sound typed)), rfl⟩
    else none

def preserve {context : Context} {input output stack : List CValType}
    (step : Body context (.plain input output))
    (stackPrefix : List CValType) (split : stackPrefix ++ input = stack)
    (valid : ResultOk context.toTypeCtx stackPrefix) : Body context (.plain stack (stackPrefix ++ output)) :=
  split ▸ .frame step valid

theorem preserve_erase {context : Context} {input output stack : List CValType}
    (step : Body context (.plain input output))
    (stackPrefix : List CValType) (split : stackPrefix ++ input = stack)
    (valid : ResultOk context.toTypeCtx stackPrefix) :
    (preserve step stackPrefix split valid).erase = step.erase := by
  subst stack
  rfl

def castResults {context : Context} {stack before after : List CValType}
    (body : Body context (.plain stack before)) (same : before = after) :
    { typed : Body context (.plain stack after) // typed.erase = body.erase } := by
  subst after
  exact ⟨body, rfl⟩

/-- Reconstruct an indexed straight-line body. The operand suffix must match exactly:
this fragment does not synthesize subtyping, control, polymorphic stacks or local writes. -/
def reifyBody? (context : Context) (stack results : List CValType) : (ops : List Instr) →
    Option { body : Body context (.plain stack results) // body.erase = ops }
  | [] =>
    if same : stack = results then
      if valid : ResultOk.check context.toTypeCtx stack = true then
        let inputEq := List.append_nil stack
        let framed := preserve (input := []) (output := []) .nil stack inputEq (ResultOk.check_sound valid)
        let ⟨typed, erased⟩ := castResults framed (inputEq.trans same)
        some ⟨typed, erased.trans (preserve_erase .nil stack inputEq (ResultOk.check_sound valid))⟩
      else none
    else none
  | op :: ops => do
    let ⟨input, output, step, eraseStep⟩ ← step? context stack op
    let stackPrefix := stack.take (stack.length - input.length)
    if split : stackPrefix ++ input = stack then
      if valid : ResultOk.check context.toTypeCtx stackPrefix = true then
        let first := preserve (.single step) stackPrefix split (ResultOk.check_sound valid)
        let ⟨rest, eraseRest⟩ ← reifyBody? context (stackPrefix ++ output) results ops
        some ⟨.seq first (by simp) rest, by
          change first.erase ++ rest.erase = op :: ops
          rw [preserve_erase, eraseRest]
          simp [Body.erase, eraseStep]⟩
      else none
    else none

/-- Reify a function against its assigned type in the enclosing module context. -/
def reifyFunction? (context : Context) (type : DefType) (func : Wasm.Func) :
    Option { typed : Function context type // typed.erase = func } := do
  if resolves : context.type? func.type = some type then
    let ⟨.func params results, expands⟩ ← type.expand?.attach | none
    let ⟨locals, valid⟩ ← (localsCheck? tyOkC context func.locals).attach
    let ⟨body, eraseBody⟩ ← reifyBody? (context.funcBody params.toList results.toList locals)
      [] results.toList func.body
    some ⟨⟨func.type, resolves, params, results, Expand.iff.mpr expands, func.locals,
      locals, localsCheck?_sound tyOkC_sound' valid, body⟩, by
        cases func
        simp only [Function.erase]
        rw [eraseBody]⟩
  else none

def functions? (context : Context) : (types : List DefType) → (raw : List Wasm.Func) →
    Option { typed : Functions context types // typed.erase = raw }
  | [], [] => some ⟨.nil, rfl⟩
  | type :: types, func :: funcs => do
    let ⟨head, eraseHead⟩ ← reifyFunction? context type func
    let ⟨tail, eraseTail⟩ ← functions? context types funcs
    some ⟨.cons head tail, by simp [Functions.erase, eraseHead, eraseTail]⟩
  | _, _ => none

/-- A checked witness holds intrinsic data and exact raw erasure, but no source bytes. -/
structure Reified (raw : Wasm.Module) where
  interface : CModuleType
  typed : Module interface
  erase_eq : typed.erase = raw

def checkEach {α : Type} (values : List α) (check : α → Bool) (Valid : α → Prop)
    (sound : ∀ value, check value = true → Valid value) : Option (PLift (∀ value ∈ values, Valid value)) :=
  if allValid : values.all check = true then
    some ⟨fun value member => sound value (List.all_eq_true.mp allValid value member)⟩
  else none

/-- Assemble intrinsic functions under the existing module checker environments. The same
 declaration checkers as `validate?` supply the non-function premises of `ModuleOk`. -/
def reify? (raw : Wasm.Module) : Option (Reified raw) := do
  let check := defaultCheckers
  let sound := defaultCheckers_sound
  let ⟨types, typesEq⟩ ← (check.types? {} raw.types).attach
  let importsContext : Context := { types := types }
  let ⟨imports, importsEq⟩ ← (raw.imports.mapM (check.import? importsContext)).attach
  let funcTypes ← raw.funcs.mapM (fun func => importsContext.type? func.type)
  let base := moduleCtx' raw types imports funcTypes
  let ⟨tags, tagsEq⟩ ← (raw.tags.mapM (check.tag? base)).attach
  let ⟨globals, globalsEq⟩ ← (check.globals? base raw.globals).attach
  let ⟨tables, tablesEq⟩ ← (raw.tables.mapM (check.table? base)).attach
  let elementTypes := raw.elems.map fun elem => base.closeRef elem.type
  let context := moduleCtx raw base imports tags globals tables elementTypes
  let ⟨funcs, eraseFuncs⟩ ← functions? context funcTypes raw.funcs
  let ⟨memoriesValid⟩ ← checkEach raw.memories check.mem MemOk (fun _ => sound.mem)
  let ⟨dataValid⟩ ← checkEach raw.data (check.data context) (DataOk context) (fun _ => sound.data)
  let ⟨exports, exportsEq⟩ ← (raw.exports.mapM (check.export? context)).attach
  if elemsEq : raw.elems.mapM (check.elem? context) = some elementTypes then
    if startEq : raw.start.all (check.start context) = true then
      if distinct : (raw.exports.map Export.name).Nodup then
        some ⟨⟨imports, exports⟩, {
          metadata := { raw with funcs := [] }
          noRawFunctions := rfl
          definedTypes := types
          definedTags := tags
          definedGlobals := globals
          definedTables := tables
          definedFuncs := funcTypes
          elementTypes := elementTypes
          baseContext := base
          context := context
          typesValid := sound.types typesEq
          importsValid := List.mapM_some_forall₂ sound.import_ importsEq
          baseContextEq := rfl
          contextEq := rfl
          tagsValid := List.mapM_some_forall₂ sound.tag tagsEq
          globalsValid := sound.globals globalsEq
          memoriesValid := memoriesValid
          tablesValid := List.mapM_some_forall₂ sound.table tablesEq
          funcs := funcs
          dataValid := dataValid
          elemsValid := List.mapM_some_forall₂ sound.elem elemsEq
          startValid := fun index equal => sound.start (by
            change raw.start = some index at equal
            rw [equal] at startEq
            exact startEq)
          exportsValid := List.mapM_some_forall₂ sound.export_ exportsEq
          exportsDisjoint := distinct }, by
            change { raw with funcs := funcs.erase } = raw
            rw [eraseFuncs]⟩
      else none
    else none
  else none

/-- The quotation command checks `success` in the kernel, on raw syntax, not on bytes. -/
def checked (raw : Wasm.Module) (success : (reify? raw).isSome = true) : Reified raw :=
  (reify? raw).get success

end Silmaril.Wasm.Validation.Intrinsic.Reify
