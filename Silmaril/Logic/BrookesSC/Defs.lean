module

public import Silmaril.Logic.Institution.Basic

/-! # Fixed-world SC signatures and open programs -/

@[expose] public section

namespace Silmaril.Logic.BrookesSC

open CategoryTheory

universe u v

/-- The identifiers and types shared by all signatures in one institution.
External reply sorts are fixed, while signatures choose their operation labels. -/
structure World where
  Thread : Type u
  Cell : Type u
  Value : Cell → Type u
  Mutex : Type u
  ExternalSort : Type u
  ExternalReply : ExternalSort → Type u

/-- Access modes share the same primitive SC store behavior. The designation is
available to subsequent observation or race analyses. -/
inductive AccessMode where
  | plain
  | scAtomic
  deriving DecidableEq

/-- One primitive in a specified thread. A write includes its typed payload. -/
inductive Primitive (W : World.{u}) where
  | load (thread : W.Thread) (mode : AccessMode) (cell : W.Cell)
  | store (thread : W.Thread) (mode : AccessMode) (cell : W.Cell) (value : W.Value cell)
  | acquire (thread : W.Thread) (mutex : W.Mutex)
  | release (thread : W.Thread) (mutex : W.Mutex)

abbrev Primitive.Reply {W : World.{u}} : Primitive W → Type u
  | .load _ _ cell => W.Value cell
  | .store .. | .acquire .. | .release .. => PUnit

/-- A label denotes either a specified primitive or an external operation
with a specified reply sort. -/
inductive Designation (W : World.{u}) where
  | primitive (step : Primitive W)
  | external (sort : W.ExternalSort)

abbrev Designation.Reply {W : World.{u}} : Designation W → Type u
  | .primitive p => p.Reply
  | .external s => W.ExternalReply s

/-- A family of operation labels classified by their full designation. -/
structure Signature (W : World.{u}) where
  Op : Designation W → Type u

variable {W : World.{u}}

/-- Arrows send labels forward in each designation fiber. The replies agree
definitionally, so there is no reply conversion. -/
structure Signature.Hom (S T : Signature W) where
  label : ∀ {d}, S.Op d → T.Op d

instance : Category (Signature W) where
  Hom := Signature.Hom
  id _ := ⟨fun op => op⟩
  comp f g := ⟨fun op => g.label (f.label op)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- A well-founded request tree. The continuation can inspect the typed reply. -/
inductive Program (S : Signature W) (A : Type u) where
  | ret (value : A)
  | call {d : Designation W} (op : S.Op d) (next : d.Reply → Program S A)

namespace Program

variable {S T : Signature W} {A : Type u}

def translate (f : S ⟶ T) : Program S A → Program T A
  | .ret value => .ret value
  | .call op next => .call (f.label op) (fun r => translate f (next r))

end Program

/-- A shared ordered target. Supply one interpretation per primitive, and
monotonicity of sequencing for comparison of models. The institution laws
use the operations directly and require no equations about sequencing. -/
structure Target (W : World.{u}) where
  Carrier : Type u → Type v
  order (A : Type u) : Preorder (Carrier A)
  pure {A : Type u} : A → Carrier A
  bind {A B : Type u} : Carrier A → (A → Carrier B) → Carrier B
  primitive (p : Primitive W) : Carrier p.Reply
  bind_mono {A B : Type u} {x y : Carrier A} {k l : A → Carrier B} :
    (order A).le x y → (∀ a, (order B).le (k a) (l a)) → (order B).le (bind x k) (bind y l)

/-- Each model supplies meanings for the external operations. Primitive
meanings come from the target, independently of their labels. -/
structure Model (D : Target.{u,v} W) (S : Signature W) where
  external : ∀ {s}, S.Op (.external s) → D.Carrier (W.ExternalReply s)

namespace Model

variable {D : Target.{u,v} W} {S T U : Signature W}

def operation (M : Model D S) : ∀ {d}, S.Op d → D.Carrier d.Reply
  | .primitive p, _ => D.primitive p
  | .external _, op => M.external op

def eval (M : Model D S) {A : Type u} : Program S A → D.Carrier A
  | .ret value => D.pure value
  | .call op next => D.bind (M.operation op) (fun r => M.eval (next r))

/-- A model arrow gives pointwise refinement of external interpretations. -/
def Refines (M N : Model D S) : Prop :=
  ∀ {s} (op : S.Op (.external s)), (D.order (W.ExternalReply s)).le (M.external op) (N.external op)

instance : Category (Model D S) where
  Hom M N := PLift (Refines M N)
  id M := ⟨fun {s} op => @le_refl _ (D.order (W.ExternalReply s)) (M.external op)⟩
  comp f g := ⟨fun {s} op => @le_trans _ (D.order (W.ExternalReply s)) _ _ _ (f.down op) (g.down op)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Reindex the external interpretation along a signature arrow. -/
def reduct (f : S ⟶ T) (M : Model D T) : Model D S :=
  ⟨fun op => M.external (f.label op)⟩

def reductFunctor (D : Target.{u,v} W) (f : S ⟶ T) : Model D T ⥤ Model D S where
  obj := reduct f
  map h := ⟨fun op => h.down (f.label op)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

end Model

/-- A universally quantified inequation between typed open programs. The
input type is the context of valuations. -/
structure Sentence (S : Signature W) where
  Input : Type u
  Result : Type u
  lhs : Input → Program S Result
  rhs : Input → Program S Result

namespace Sentence

variable {D : Target.{u,v} W} {S T : Signature W}

def translate (f : S ⟶ T) (e : Sentence S) : Sentence T :=
  ⟨e.Input, e.Result, fun x => (e.lhs x).translate f, fun x => (e.rhs x).translate f⟩

def Satisfies (M : Model D S) (e : Sentence S) : Prop :=
  ∀ x, (D.order e.Result).le (M.eval (e.lhs x)) (M.eval (e.rhs x))

end Sentence

end Silmaril.Logic.BrookesSC
