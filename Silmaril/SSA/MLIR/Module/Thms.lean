module

public import Silmaril.SSA.MLIR.Module.Defs

/-! Map laws and the natural identification of the generic and typed module views. -/

public section

namespace Silmaril.MLIR

universe u v w u' v' w' u'' v'' w''

@[simp] theorem Module.map_id {F : Type u} (mod : Module F) :
    Module.map id mod = mod := by cases mod; simp [map]

theorem Module.map_comp {F : Type u} {G : Type v} {H : Type w}
    (f : F → G) (g : G → H) (mod : Module F) :
    Module.map g (Module.map f mod) = Module.map (g ∘ f) mod := by simp [map, List.map_map]

variable {I : Type u} {O : Type v} {I' : Type u'} {O' : Type v'} {I'' : Type u''} {O'' : Type v''}
  {B : I → O → Type w} {C : I' → O' → Type w'} {D : I'' → O'' → Type w''}

@[simp] theorem FuncOf.map_id (fn : FuncOf B) :
    fn.map id id (fun body => body) = fn := by cases fn; rfl

theorem FuncOf.map_comp (f : I → I') (g : O → O') (h : I' → I'') (k : O' → O'')
    (first : ∀ {i o}, B i o → C (f i) (g o)) (second : ∀ {i o}, C i o → D (h i) (k o))
    (fn : FuncOf B) : (fn.map f g first).map h k second =
      fn.map (h ∘ f) (k ∘ g) (fun body => second (first body)) := rfl

@[simp] theorem FuncModule.ofModule_toModule (mod : FuncModule B) :
    ofModule mod.toModule = mod := rfl

@[simp] theorem FuncModule.toModule_ofModule (mod : Module (FuncOf B)) :
    (ofModule mod).toModule = mod := rfl

/-- The identification commutes with typed translation on every function. -/
theorem FuncModule.toModule_map (f : I → I') (g : O → O')
    (body : ∀ {i o}, B i o → C (f i) (g o)) (mod : FuncModule B) :
    (mod.map f g body).toModule = Module.map (FuncOf.map f g body) mod.toModule := rfl

theorem FuncModule.ofModule_map (f : I → I') (g : O → O')
    (body : ∀ {i o}, B i o → C (f i) (g o)) (mod : Module (FuncOf B)) :
    ofModule (Module.map (FuncOf.map f g body) mod) = (ofModule mod).map f g body := rfl

@[simp] theorem FuncModule.map_id (mod : FuncModule B) :
    mod.map id id (fun body => body) = mod := by
  have identity : FuncOf.map (B := B) id id (fun body => body) = id := funext FuncOf.map_id
  simp [map, identity]

theorem FuncModule.map_comp (f : I → I') (g : O → O') (h : I' → I'') (k : O' → O'')
    (first : ∀ {i o}, B i o → C (f i) (g o)) (second : ∀ {i o}, C i o → D (h i) (k o))
    (mod : FuncModule B) : (mod.map f g first).map h k second =
      mod.map (h ∘ f) (k ∘ g) (fun body => second (first body)) :=
  Module.map_comp (FuncOf.map f g first) (FuncOf.map h k second) mod

@[simp] theorem FuncModule.find?_map (f : I → I') (g : O → O')
    (body : ∀ {i o}, B i o → C (f i) (g o)) (mod : FuncModule B) (name : String) :
    (mod.map f g body).find? name = (mod.find? name).map (FuncOf.map f g body) :=
  List.find?_map

end Silmaril.MLIR
