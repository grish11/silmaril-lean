module

public import Silmaril.Logic.Temporal.Buchi.Automaton.Thms
public import Silmaril.Logic.ModalMu.Thms

@[expose] public section
namespace Silmaril.Logic.Temporal.Buchi.Automaton
open CategoryTheory

/-- Finite propositional transition guards. Negation occurs only at atoms;
guards have no modal operators, set variables or semantic oracle constructors. -/
inductive Guard (Atom : Type) where
  | pos : Atom → Guard Atom
  | neg : Atom → Guard Atom
  | top : Guard Atom
  | bot : Guard Atom
  | conj : Guard Atom → Guard Atom → Guard Atom
  | disj : Guard Atom → Guard Atom → Guard Atom

def Guard.Holds {Atom : Type} (letter : Atom → Prop) : Guard Atom → Prop
  | .pos a => letter a
  | .neg a => ¬ letter a
  | .top => True
  | .bot => False
  | .conj p q => p.Holds letter ∧ q.Holds letter
  | .disj p q => p.Holds letter ∨ q.Holds letter

def Guard.map {Atom Atom' : Type} (f : Atom → Atom') : Guard Atom → Guard Atom'
  | .pos a => .pos (f a)
  | .neg a => .neg (f a)
  | .top => .top
  | .bot => .bot
  | .conj p q => .conj (p.map f) (q.map f)
  | .disj p q => .disj (p.map f) (q.map f)

theorem Guard.holds_map {Atom Atom' : Type} (f : Atom → Atom') (letter : Atom' → Prop)
    (g : Guard Atom) : (g.map f).Holds letter ↔ g.Holds (letter ∘ f) := by
  induction g <;> simp_all [Guard.map, Guard.Holds, Function.comp_def]

/-- Actual modal μ syntax for every finite guard, at any free-variable scope. -/
def Guard.toFormula {S : ModalMu.Signature} {k : Nat} : Guard S.Atom → ModalMu.Formula S k
  | .pos a => .pos a
  | .neg a => .neg a
  | .top => .top
  | .bot => .bot
  | .conj p q => .conj p.toFormula q.toFormula
  | .disj p q => .disj p.toFormula q.toFormula

theorem Guard.toFormula_denote {S : ModalMu.Signature} (M : ModalMu.Model S)
    {k : Nat} (ρ : ModalMu.Env M.World k) (g : Guard S.Atom) (w : M.World) :
    w ∈ g.toFormula.denote M ρ ↔ g.Holds (fun a => w ∈ M.valuation a) := by
  induction g with
  | pos a => rfl
  | neg a => rfl
  | top => exact Iff.rfl
  | bot => exact Iff.rfl
  | conj p q hp hq =>
    change (_ ∧ _) ↔ (_ ∧ _)
    exact and_congr hp hq
  | disj p q hp hq =>
    change (_ ∨ _) ↔ (_ ∨ _)
    exact or_congr hp hq

theorem Guard.toFormula_map {S T : ModalMu.Signature} (f : S ⟶ T) {k : Nat}
    (g : Guard S.Atom) :
    (g.toFormula : ModalMu.Formula S k).map f = (g.map f.atom).toFormula := by
  induction g <;> simp_all [Guard.toFormula, Guard.map, ModalMu.Formula.map]

/-- A concrete finite symbolic automaton: one finite guard for each state pair.
Disjunction represents alternatives on an edge; multiple target states remain
nondeterministic. The alphabet is the actual current atom valuation. -/
structure Symbolic (Atom : Type) (n : Nat) where
  initial : Set (Fin n)
  guard : Fin n → Fin n → Guard Atom
  accepting : Set (Fin n)

def Symbolic.automaton {Atom : Type} {n : Nat} (A : Symbolic Atom n) :
    Buchi.Automaton (Atom → Prop) n where
  initial := A.initial
  step q letter r := (A.guard q r).Holds letter
  accepting := A.accepting

def Symbolic.map {Atom Atom' : Type} {n : Nat} (A : Symbolic Atom n) (f : Atom → Atom') :
    Symbolic Atom' n where
  initial := A.initial
  guard q r := (A.guard q r).map f
  accepting := A.accepting

/-- Read each world's current atom predicates as its input letter. -/
def modelLabel {S : ModalMu.Signature} (M : ModalMu.Model S) (w : M.World) : S.Atom → Prop :=
  fun a => w ∈ M.valuation a

def Symbolic.AcceptsModel {S : ModalMu.Signature} {n : Nat} (A : Symbolic S.Atom n)
    (M : ModalMu.Model S) (a : S.Action) : Prop :=
  A.automaton.AcceptsPath (M.step a) (modelLabel M) M.point

/-- The actual guard formula plus one graph edge is exactly a product edge.
This is the concrete interface for a later finite-equation compiler. -/
theorem Symbolic.productStep_iff {S : ModalMu.Signature} {n k : Nat}
    (A : Symbolic S.Atom n) (M : ModalMu.Model S) (a : S.Action)
    (ρ : ModalMu.Env M.World k) (w v : M.World) (q r : Fin n) :
    A.automaton.productStep (M.step a) (modelLabel M) (w, q) (v, r) ↔
      M.step a w v ∧ w ∈ (A.guard q r).toFormula.denote M ρ := by
  exact and_congr_right (fun _ => (Guard.toFormula_denote M ρ (A.guard q r) w).symm)

theorem Symbolic.acceptsModel_iff_gfp {S : ModalMu.Signature} {n : Nat}
    (A : Symbolic S.Atom n) (M : ModalMu.Model S) (a : S.Action) :
    A.AcceptsModel M a ↔ ∃ q ∈ A.initial,
      (M.point, q) ∈ (Buchi.outer
        (A.automaton.productStep (M.step a) (modelLabel M)) A.automaton.productAccepting).gfp :=
  acceptsPath_iff_gfp A.automaton (M.step a) (modelLabel M) M.point

/-- Named atom/action pullback: renamed guards on a target model have exactly
the source guard meaning on its reduct. The same world and state pairs remain. -/
theorem Symbolic.productStep_map {S T : ModalMu.Signature} {n : Nat}
    (A : Symbolic S.Atom n) (f : S ⟶ T) (M : ModalMu.Model T) (a : S.Action)
    (x y : M.World × Fin n) :
    (A.map f.atom).automaton.productStep (M.step (f.action a)) (modelLabel M) x y ↔
      A.automaton.productStep ((ModalMu.reduct f M).step a)
        (modelLabel (ModalMu.reduct f M)) x y := by
  exact and_congr_right (fun _ => Guard.holds_map f.atom (modelLabel M x.1) (A.guard x.2 y.2))

theorem Symbolic.acceptsModel_map {S T : ModalMu.Signature} {n : Nat}
    (A : Symbolic S.Atom n) (f : S ⟶ T) (M : ModalMu.Model T) (a : S.Action) :
    (A.map f.atom).AcceptsModel M (f.action a) ↔ A.AcceptsModel (ModalMu.reduct f M) a := by
  simp [Symbolic.AcceptsModel, AcceptsPath, Accepts, IsPath, IsRun, Recurrent,
    Symbolic.map, Symbolic.automaton, modelLabel, Guard.holds_map, ModalMu.reduct,
    Function.comp_def]
  rfl

end Silmaril.Logic.Temporal.Buchi.Automaton
