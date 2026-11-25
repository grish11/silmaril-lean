module

public import Init.Data.List.Find

/-! # Typed MLIR function modules

The body family determines the types of the input and output interfaces.
A module stores the named declarations in order with distinct symbols.
-/

@[expose] public section

namespace Silmaril.MLIR

universe u v w u' v' w'

/-- An ordered table of function declarations with unique symbol names. -/
structure Module (Func : Type u) where
  funcs : List (String × Func)
  uniqueNames : (funcs.map Prod.fst).Nodup

/-- Translate the functions at the same symbols in the same order. -/
def Module.map {F : Type u} {G : Type v} (f : F → G) (mod : Module F) : Module G where
  funcs := mod.funcs.map (Prod.map id f)
  uniqueNames := by simpa [List.map_map, Function.comp_def] using mod.uniqueNames

/-- Look up a function by its module symbol. -/
def Module.find? {F : Type u} (mod : Module F) (name : String) : Option F :=
  mod.funcs.lookup name

/-- A function definition with a body typed at its declared interface. -/
structure FuncOf {I : Type u} {O : Type v} (Body : I → O → Type w) where
  inputs : I
  outputs : O
  body : Body inputs outputs

variable {I : Type u} {O : Type v} {I' : Type u'} {O' : Type v'}
  {B : I → O → Type w} {C : I' → O' → Type w'}

/-- Translate the function's interface and its body at that interface. -/
def FuncOf.map (inputs : I → I') (outputs : O → O')
    (body : ∀ {i o}, B i o → C (inputs i) (outputs o)) (fn : FuncOf B) : FuncOf C :=
  ⟨inputs fn.inputs, outputs fn.outputs, body fn.body⟩

/-- The typed view of `Module (FuncOf Body)`, with the same representation. -/
abbrev FuncModule (Body : I → O → Type w) := Module (FuncOf Body)

def FuncModule.toModule (mod : FuncModule B) : Module (FuncOf B) := mod

def FuncModule.ofModule (mod : Module (FuncOf B)) : FuncModule B := mod

/-- Translate every declaration at its own interface, preserving names and order. -/
def FuncModule.map (inputs : I → I') (outputs : O → O')
    (body : ∀ {i o}, B i o → C (inputs i) (outputs o)) (mod : FuncModule B) : FuncModule C :=
  Module.map (FuncOf.map inputs outputs body) mod

/-- Find the function at this symbol, retaining its interface and typed body. -/
abbrev FuncModule.find? (mod : FuncModule B) (name : String) : Option (FuncOf B) :=
  Module.find? mod name

end Silmaril.MLIR
