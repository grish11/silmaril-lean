module

public import Silmaril.Logic.Temporal.Buchi.Automaton.Thms
public import Silmaril.Logic.Temporal.Buchi.Modal

@[expose] public section
namespace Silmaril.Logic.Temporal.Buchi.Automaton

/-- A single product edge action and a fresh accepting-state atom. -/
def productSignature : ModalMu.Signature := ⟨Unit, Unit⟩

def productModel {Letter W : Type} {n : Nat} (A : Buchi.Automaton Letter n)
    (R : W → W → Prop) (label : W → Letter) (w : W) (q : Fin n) :
    ModalMu.Model productSignature where
  World := W × Fin n
  step _ := A.productStep R label
  valuation _ := A.productAccepting
  point := (w, q)

/-- Actual scalar modal μ syntax, interpreted on the synchronized product. -/
def acceptingRunFormula : ModalMu.Formula productSignature 0 :=
  Buchi.infinitelyOften () ()

theorem acceptingRunFormula_iff {Letter W : Type} {n : Nat}
    (A : Buchi.Automaton Letter n) (R : W → W → Prop) (label : W → Letter)
    (w : W) (q : Fin n) :
    ModalMu.Sat (productModel A R label w q) acceptingRunFormula ↔
      Buchi.Accepts (A.productStep R label) A.productAccepting (w, q) :=
  Buchi.infinitelyOften_iff (productModel A R label w q) () () (w, q)

/-- One accepting graph path/run is equivalent to the actual closed formula at
some initial product point. It is not yet a formula on the original base graph. -/
theorem acceptsPath_iff_formula {Letter W : Type} {n : Nat}
    (A : Buchi.Automaton Letter n) (R : W → W → Prop) (label : W → Letter) (w : W) :
    A.AcceptsPath R label w ↔ ∃ q ∈ A.initial,
      ModalMu.Sat (productModel A R label w q) acceptingRunFormula := by
  rw [acceptsPath_iff_product]
  simp only [acceptingRunFormula_iff]

end Silmaril.Logic.Temporal.Buchi.Automaton
