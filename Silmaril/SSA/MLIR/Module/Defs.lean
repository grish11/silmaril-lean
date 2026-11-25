module

public import Init.Data.List.Find

/-! # Typed MLIR function modules

The body family determines the types of the input and output interfaces.
A module stores its function declarations in order.
-/

@[expose] public section

namespace Silmaril.MLIR

universe u v w u' v' w'

/-- An ordered collection of function declarations. -/
structure Module (Func : Type u) where
  funcs : List Func

def Module.map {F : Type u} {G : Type v} (f : F → G) (mod : Module F) : Module G :=
  ⟨mod.funcs.map f⟩

/-- A named function definition with a body typed at its declared interface. -/
structure FuncOf {I : Type u} {O : Type v} (Body : I → O → Type w) where
  name : String
  inputs : I
  outputs : O
  body : Body inputs outputs

variable {I : Type u} {O : Type v} {I' : Type u'} {O' : Type v'}
  {B : I → O → Type w} {C : I' → O' → Type w'}

/-- Translate the interface and body of a function while preserving its name. -/
def FuncOf.map (inputs : I → I') (outputs : O → O')
    (body : ∀ {i o}, B i o → C (inputs i) (outputs o)) (fn : FuncOf B) : FuncOf C :=
  ⟨fn.name, inputs fn.inputs, outputs fn.outputs, body fn.body⟩

/-- The typed view of `Module (FuncOf Body)`, with the same representation. -/
abbrev FuncModule (Body : I → O → Type w) := Module (FuncOf Body)

def FuncModule.toModule (mod : FuncModule B) : Module (FuncOf B) := mod

def FuncModule.ofModule (mod : Module (FuncOf B)) : FuncModule B := mod

/-- Translate every declaration at its own interface, preserving names and order. -/
def FuncModule.map (inputs : I → I') (outputs : O → O')
    (body : ∀ {i o}, B i o → C (inputs i) (outputs o)) (mod : FuncModule B) : FuncModule C :=
  Module.map (FuncOf.map inputs outputs body) mod

/-- Find the first definition with this name, retaining its interface and typed body. -/
def FuncModule.find? (mod : FuncModule B) (name : String) : Option (FuncOf B) :=
  mod.funcs.find? (fun fn => fn.name == name)

end Silmaril.MLIR
