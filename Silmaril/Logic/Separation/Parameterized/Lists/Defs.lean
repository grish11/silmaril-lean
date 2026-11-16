module

public import Silmaril.Logic.Separation.Parameterized.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Separation.Parameterized.Lists

inductive Operation : Nat → Type where
  | nil : Operation 0
inductive Atom : Nat → Type where
  | link : Atom 2

def signature : Signature := ⟨Operation, Atom⟩
def nilTerm {k} : Term signature k := .app .nil (fun i => i.elim0)
def link {k} (x y : Term signature k) : Assertion signature k :=
  .atom .link (Fin.cases x (fun _ => y))

/-- μL(x). (x=nil ∧ emp) ∨ ∃y. (x≠nil ∧ x↦y) * L(y).
The fresh existential pointer is actually passed to the recursive call. -/
def body : Pattern signature (fun _ : Fin 1 => 1) 2 :=
  .disj (.base (.conj (.eq (.var 0) nilTerm) .emp))
    (.ex (.sep (.base (.conj (.neg (.eq (.var 1) nilTerm)) (link (.var 1) (.var 0))))
      (.pred 0 (fun _ => .var 0))))

def list : Pattern signature (fun _ : Fin 0 => 1) 1 :=
  .lfp (P' := fun _ : Fin 1 => 1) body (fun _ => .var 0)

def null (M : Model signature) : M.Value := M.operation Operation.nil (fun i => i.elim0)
def cell (M : Model signature) (x y : M.Value) : Set M.resource.carrier :=
  M.atom Atom.link (Fin.cases x (fun _ => y))

/-- Independent finite linked shape on arbitrary resources. No compiler,
fixed-point denotation, finiteness test or iteration budget is an input. -/
inductive Linked (M : Model signature) : M.Value → M.resource.carrier → Prop where
  | nil : Linked M (null M) M.resource.unit
  | cons {x y a b h} (nonnull : x ≠ null M) (head : a ∈ cell M x y)
      (joined : M.resource.join a b h) (tail : Linked M y b) : Linked M x h

def step (M : Model signature) (X : Set (State M 1)) : Set (State M 1) :=
  {s | (s.1 0 = null M ∧ s.2 = M.resource.unit) ∨
    ∃ y a b, s.1 0 ≠ null M ∧ a ∈ cell M (s.1 0) y ∧
      M.resource.join a b s.2 ∧ ((fun _ => y), b) ∈ X}

end Silmaril.Logic.Separation.Parameterized.Lists
