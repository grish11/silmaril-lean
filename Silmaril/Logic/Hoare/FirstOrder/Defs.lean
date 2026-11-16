module

public import Silmaril.Logic.Hoare.Thms
public import Silmaril.Logic.Institution.Examples.FirstOrder

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Hoare.FirstOrder
open CategoryTheory Silmaril.Logic.Institution.Examples

abbrev Value {A : FOL.Signature} (M : FOL.Structure A) := Sigma M.carrier
/-- Partial typed stores remain inhabited even when all source carriers are empty. -/
abbrev Store {A : FOL.Signature} (M : FOL.Structure A) := Nat → Option (Value M)

def empty {A : FOL.Signature} (M : FOL.Structure A) : Store M := fun _ => none

/-- New binders occupy the next slot; old variables retain their slots. -/
def slot {k : Nat} (i : Fin k) : Nat := k - 1 - i.val

def Encodes {A : FOL.Signature} (M : FOL.Structure A) {k} (Γ : Fin k → A.S)
    (ρ : ∀ i, M.carrier (Γ i)) (h : Store M) : Prop :=
  ∀ i, h (slot i) = some ⟨Γ i, ρ i⟩

/-- Only actual term equality and primitive relation observations are labels. -/
inductive Atom (A : FOL.Signature) where
  | eq {k} (Γ : Fin k → A.S) {s} (t u : EQ.Term A.toSignature Γ s)
  | rel {k} (Γ : Fin k → A.S) {n w} (r : A.Rel n w)
      (args : ∀ j, EQ.Term A.toSignature Γ (w j))

abbrev language (A : FOL.Signature) : PDL.Signature := ⟨Atom A, Nat × A.S⟩

/-- Nondeterministic assignment writes one value and leaves every other slot alone. -/
def havoc {A : FOL.Signature} (M : FOL.Structure A) (a : Nat × A.S)
    (h h' : Store M) : Prop :=
  ∃ x : M.carrier a.2, h' = Function.update h a.1 (some ⟨a.2, x⟩)

def atom {A : FOL.Signature} (M : FOL.Structure A) : Atom A → Set (Store M)
  | .eq Γ t u => {h | ∃ ρ, Encodes M Γ ρ h ∧ t.eval M.toAlgebra ρ = u.eval M.toAlgebra ρ}
  | .rel Γ r args => {h | ∃ ρ, Encodes M Γ ρ h ∧ M.rel r (fun j => (args j).eval M.toAlgebra ρ)}

/-- An independent native PDL frame, computed from the actual first-order structure. -/
def native {A : FOL.Signature} (M : FOL.Structure A) : PDL.Model (language A) :=
  ⟨Store M, havoc M, atom M, empty M⟩

def truth {A : FOL.Signature} : PDL.Formula (language A) := .neg .bot

/-- Structural quantifier compilation uses native modal boxes over real havoc steps. -/
def compile {A : FOL.Signature} : {k : Nat} → {Γ : Fin k → A.S} →
    FOL.Formula A Γ → PDL.Formula (language A)
  | _, _, .eq t u => .atom (.eq _ t u)
  | _, _, .rel r args => .atom (.rel _ r args)
  | _, _, .tt => truth
  | _, _, .not φ => .neg (compile φ)
  | _, _, .and φ ψ => .conj (compile φ) (compile ψ)
  | k, _, .all (Δ := Δ) _ φ => .box (.action (k, Δ 0)) (compile φ)

/-- Both skip and every slot/sort havoc are genuine named native Hoare commands. -/
abbrev Command (S : Type) := Option (Nat × S)

def signature (A : FOL.Signature) : Hoare.Signature (Command A.S) where
  language := language A
  body c := match c with
    | none => .test truth
    | some a => .action a

/-- Closed FOL sentences become ordinary global partial-correctness skip triples. -/
def sentence {A : FOL.Signature} (φ : FOL.Sentence A) : Hoare.Triple (Command A.S) (signature A) :=
  ⟨none, truth, compile φ.formula⟩

end Silmaril.Logic.Hoare.FirstOrder
