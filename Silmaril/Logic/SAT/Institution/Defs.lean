module

public import Silmaril.Logic.SAT.CNF.Defs

@[expose] public section

/-! # Valuation semantics of CNF over arbitrary atom types -/

namespace Silmaril.Logic.SAT.Institution

universe u v w

/-- A signed atom. Keeping polarity separate lets signature maps identify atoms freely. -/
structure Literal (A : Type u) where
  atom : A
  positive : Bool

/-- A disjunction of signed atoms. -/
abbrev Clause (A : Type u) := List (Literal A)

/-- A SAT problem is a conjunction of clauses over the given signature. -/
abbrev Problem (A : Type u) := List (Clause A)

variable {A : Type u} {B : Type v}

def Literal.rename (f : A → B) (l : Literal A) : Literal B := ⟨f l.atom, l.positive⟩

def Problem.rename (f : A → B) (F : Problem A) : Problem B := F.map (·.map (Literal.rename f))

/-- Read the existing integer syntax using its variable and polarity operations. -/
def Problem.ofCNF (F : SAT.CNF) : Problem Nat := F.map (·.map fun l => ⟨l.var, l.pos⟩)

/-- Reduce a target valuation by precomposition with a signature map. -/
def reduct {V : Type w} (f : A → B) (v : B → V) : A → V := v ∘ f

/-- A valuation in the strong Kleene algebra, with `none` for unknown. -/
abbrev PartialValuation (A : Type u) := A → Option Bool

abbrev TotalValuation (A : Type u) := A → Bool

namespace K3

def neg (a : Option Bool) : Option Bool := a.map Bool.not

def conj : Option Bool → Option Bool → Option Bool
  | some false, _ | _, some false => some false
  | some true, some true => some true
  | _, _ => none

def disj : Option Bool → Option Bool → Option Bool
  | some true, _ | _, some true => some true
  | some false, some false => some false
  | _, _ => none

/-- Information order: an unknown can become known, and a known result is preserved. -/
def InformationLE (a b : Option Bool) : Prop := ∀ x, a = some x → b = some x

end K3

/-- Independent positive (support) and negative (refutation) evidence. -/
@[ext] structure Evidence where
  support : Bool
  refute : Bool
  deriving DecidableEq

abbrev EvidenceValuation (A : Type u) := A → Evidence

namespace Evidence

def neither : Evidence := ⟨false, false⟩
def trueOnly : Evidence := ⟨true, false⟩
def falseOnly : Evidence := ⟨false, true⟩
def both : Evidence := ⟨true, true⟩

def neg (a : Evidence) : Evidence := ⟨a.refute, a.support⟩

def conj (a b : Evidence) : Evidence := ⟨a.support && b.support, a.refute || b.refute⟩

def disj (a b : Evidence) : Evidence := ⟨a.support || b.support, a.refute && b.refute⟩

/-- Truth order: increasing support and decreasing refutation. -/
def TruthLE (a b : Evidence) : Prop :=
  (a.support = true → b.support = true) ∧ (b.refute = true → a.refute = true)

/-- Information order: increasing evidence in both channels. -/
def InformationLE (a b : Evidence) : Prop :=
  (a.support = true → b.support = true) ∧ (a.refute = true → b.refute = true)

/-- A strong Kleene value has at most one kind of evidence. -/
def ofK3 : Option Bool → Evidence
  | none => neither
  | some true => trueOnly
  | some false => falseOnly

end Evidence

/-- Evaluate a signed atom using the chosen negation. -/
def Literal.evalWith {V : Type w} (neg : V → V) (v : A → V) (l : Literal A) : V :=
  if l.positive then v l.atom else neg (v l.atom)

/-- Fold a clause as a disjunction, with `bot` for the empty clause. -/
def Clause.evalWith {V : Type w} (bot : V) (neg : V → V) (disj : V → V → V)
    (v : A → V) (C : Clause A) : V :=
  C.foldr (fun l acc => disj (l.evalWith neg v) acc) bot

namespace Problem

/-- Interpret signed atoms, clause disjunction and problem conjunction in a truth algebra. -/
def evalWith {V : Type w} (top bot : V) (neg : V → V) (conj disj : V → V → V)
    (v : A → V) (F : Problem A) : V :=
  F.foldr (fun C acc => conj (Clause.evalWith bot neg disj v C) acc) top

/-- Classical evaluation under a total Boolean assignment. -/
def eval (v : TotalValuation A) (F : Problem A) : Bool :=
  F.all fun C => C.any fun l => v l.atom == l.positive

/-- Compositional strong Kleene evaluation. -/
def evalK3 (v : PartialValuation A) (F : Problem A) : Option Bool :=
  F.evalWith (some true) (some false) K3.neg K3.conj K3.disj v

/-- Compositional Belnap/FDE evaluation (conjunction and disjunction in the truth order). -/
def evalEvidence (v : EvidenceValuation A) (F : Problem A) : Evidence :=
  F.evalWith Evidence.trueOnly Evidence.falseOnly Evidence.neg Evidence.conj Evidence.disj v

end Problem

/-- A total assignment completes a partial one when it agrees at every known atom. -/
def Completes (v : PartialValuation A) (t : TotalValuation A) : Prop :=
  ∀ a b, v a = some b → t a = b

/-- Every completion of the reduct lifts to a completion of the target valuation. -/
def CompletionCovers (f : A → B) (v : PartialValuation B) : Prop :=
  ∀ s, Completes (reduct f v) s → ∃ t, Completes v t ∧ reduct f t = s

/-- Independent universal satisfaction and refutation over total completions. -/
noncomputable def Problem.completionEvidence (v : PartialValuation A) (F : Problem A) : Evidence :=
  letI := Classical.propDecidable
  ⟨decide (∀ t, Completes v t → F.eval t = true),
   decide (∀ t, Completes v t → F.eval t = false)⟩

/-- Supervaluation is true or false when all completions agree, and unknown when they split. -/
noncomputable def Problem.superEval (v : PartialValuation A) (F : Problem A) : Option Bool :=
  let e := F.completionEvidence v
  if e.support then some true
  else if e.refute then some false
  else none

end Silmaril.Logic.SAT.Institution
