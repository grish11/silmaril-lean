module

public import Silmaril.Logic.Modal.Thms
public import Silmaril.Logic.Institution.Borrowing

@[expose] public section
namespace Silmaril.Logic.CTL
open CategoryTheory Silmaril.Logic.Institution

abbrev Signature := Modal.Signature

inductive Formula (S : Signature)
  | atom : S.Atom → Formula S
  | bot : Formula S
  | neg : Formula S → Formula S
  | conj : Formula S → Formula S → Formula S
  | ex : Formula S → Formula S
  | eu : Formula S → Formula S → Formula S
  | eg : Formula S → Formula S

/-- A finite path reaches Q, with P at every strictly earlier state. -/
inductive Until {W : Type} (R : W → W → Prop) (P Q : W → Prop) : W → Prop
  | now {w} : Q w → Until R P Q w
  | next {w v} : P w → R w v → Until R P Q v → Until R P Q w

/-- A genuine infinite path; deadlocks have none. -/
def Globally {W : Type} (R : W → W → Prop) (P : W → Prop) (w : W) : Prop :=
  ∃ path : Nat → W, path 0 = w ∧ (∀ n, R (path n) (path (n+1))) ∧ ∀ n, P (path n)

/-- Eventuality on every infinite path and every finite path ending at a deadlock. -/
def AllEventually {W : Type} (R : W → W → Prop) (P : W → Prop) (w : W) : Prop :=
  (∀ path : Nat → W, path 0 = w → (∀ n, R (path n) (path (n+1))) → ∃ n, P (path n)) ∧
  (∀ (n : Nat) (path : Nat → W), path 0 = w →
    (∀ i, i < n → R (path i) (path (i+1))) → (∀ v, ¬ R (path n) v) →
      ∃ i, i ≤ n ∧ P (path i))

/-- Strong until on all infinite and finite deadlock-ending paths. -/
def AllUntil {W : Type} (R : W → W → Prop) (P Q : W → Prop) (w : W) : Prop :=
  (∀ path : Nat → W, path 0 = w → (∀ n, R (path n) (path (n+1))) →
    ∃ n, Q (path n) ∧ ∀ i, i < n → P (path i)) ∧
  (∀ (n : Nat) (path : Nat → W), path 0 = w →
    (∀ i, i < n → R (path i) (path (i+1))) → (∀ v, ¬ R (path n) v) →
      ∃ j, j ≤ n ∧ Q (path j) ∧ ∀ i, i < j → P (path i))

/-- The frame and valuation are those of public K; arrows are equality-only. -/
structure Model (S : Signature) where
  toModal : Modal.Model S

instance (S : Signature) : Category (Model S) where
  Hom M N := PLift (M = N)
  id _ := ⟨rfl⟩
  comp f g := ⟨f.down.trans g.down⟩

def Formula.Holds {S : Signature} (M : Model S) : Formula S → M.toModal.World → Prop
  | .atom a, w => M.toModal.valuation a w
  | .bot, _ => False
  | .neg p, w => ¬ p.Holds M w
  | .conj p q, w => p.Holds M w ∧ q.Holds M w
  | .ex p, w => ∃ v, M.toModal.accessible w v ∧ p.Holds M v
  | .eu p q, w => Until M.toModal.accessible (p.Holds M) (q.Holds M) w
  | .eg p, w => Globally M.toModal.accessible (p.Holds M) w

def Sat {S : Signature} (M : Model S) (p : Formula S) : Prop := p.Holds M M.toModal.point

def Formula.map {S T : Signature} (f : S ⟶ T) : Formula S → Formula T
  | .atom a => .atom (f a)
  | .bot => .bot
  | .neg p => .neg (p.map f)
  | .conj p q => .conj (p.map f) (q.map f)
  | .ex p => .ex (p.map f)
  | .eu p q => .eu (p.map f) (q.map f)
  | .eg p => .eg (p.map f)

def reduct {S T : Signature} (f : S ⟶ T) (M : Model T) : Model S :=
  ⟨(Modal.reduct f).obj M.toModal⟩

def modelReduct {S T : Signature} (f : S ⟶ T) : Model T ⥤ Model S where
  obj := reduct f
  map h := ⟨congrArg (reduct f) h.down⟩

/-- Ordinary Boolean abbreviations. -/
def Formula.top {S : Signature} : Formula S := .neg .bot
def Formula.disj {S : Signature} (p q : Formula S) : Formula S := .neg (.conj (.neg p) (.neg q))
def Formula.imp {S : Signature} (p q : Formula S) : Formula S := .disj (.neg p) q
/-- Weak AX is the modal-K box: vacuously true at a deadlock. -/
def Formula.ax {S : Signature} (p : Formula S) : Formula S := .neg (.ex (.neg p))
def Formula.ef {S : Signature} (p : Formula S) : Formula S := .eu .top p
/-- Every finite reachable state satisfies p, including terminal states. -/
def Formula.ag {S : Signature} (p : Formula S) : Formula S := .neg (.ef (.neg p))
def Formula.deadlock {S : Signature} : Formula S := .neg (.ex .top)
/-- Eventuality on every maximal path, including finite paths ending at a deadlock. -/
def Formula.af {S : Signature} (p : Formula S) : Formula S :=
  .conj (.neg (.eg (.neg p))) (.neg (.eu (.neg p) (.conj .deadlock (.neg p))))
/-- Strong until on every maximal path: exclude a bad state, endless delay and terminal delay. -/
def Formula.au {S : Signature} (p q : Formula S) : Formula S :=
  .conj (.neg (.eu (.neg q) (.conj (.neg p) (.neg q)))) (.af q)

end Silmaril.Logic.CTL
