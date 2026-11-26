module

public import Silmaril.SSA.Isotope.LetCase.HandledTrace.Category.Defs
public import Silmaril.SSA.Isotope.Refinement.Models.Defs
import Silmaril.Proofs.SSA.Isotope.LetCase.HandledTrace.Category.Order

@[expose] public section

namespace Silmaril.Isotope.LetCase.HandledTrace

open CategoryTheory Silmaril.Isotope.Semantics Silmaril.Elgot.ITree
open Silmaril.Isotope.Refinement.Models (OrderedCategory)

universe u v e s

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {D : τ → Type (e + 1)} [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
  {Events : Type e → Type e} {State : Type s}
  {M : InstructionModel D Φ (Tree Events)} {policy : Handler State Events}

namespace Program

variable {A B C : τ}

/-- Inserting an older input slot below the body's input preserves its native run. -/
theorem run_underBinder (q : Program Φ B C) (a : D A) (b : D B) :
    q.2.underBinder.denote D M (fun x => Empty.elim x)
      ((BoundEnv.snoc (β := .nil) (fun i => i.elim0) a).snoc b) = q.run M b :=
  Proofs.run_underBinder q a b

/-- Native sequencing implements ITree bind on the complete intermediate value. -/
theorem run_seq (p : Program Φ A B) (q : Program Φ B C) (a : D A) :
    (p.seq q).run M a = (p.run M a >>= q.run M) :=
  Proofs.run_seq p q a

/-- Uniformly comparing continuations supplies the reachable cases needed by
the handled bind law. -/
theorem seq_mono {p p' : Program Φ A B} {q q' : Program Φ B C}
    (hp : Refines M policy p p') (hq : Refines M policy q q') :
    Refines M policy (p.seq q) (p'.seq q') :=
  Proofs.seq_mono hp hq

/-- Equal typed runs give the same class under every fixed reply policy. -/
theorem equiv_of_run_eq {p q : Program Φ A B} (eq : ∀ a, p.run M a = q.run M a) :
    (setoid M policy A B).r p q :=
  ⟨fun a _ => eq a ▸ .refl _, fun a _ => (eq a).symm ▸ .refl _⟩

end Program

namespace Arrow

variable {A B C : Interface M policy}

/-- Native sequencing descends to observational classes. -/
def seq : Arrow A B → Arrow B C → Arrow A C :=
  Quotient.map₂' Program.seq (by
    intro p p' hp q q' hq
    exact ⟨Program.seq_mono hp.1 hq.1, Program.seq_mono hp.2 hq.2⟩)

theorem seq_mono {p p' : Arrow A B} {q q' : Arrow B C}
    (hp : Arrow.le p p') (hq : Arrow.le q q') : Arrow.le (seq p q) (seq p' q') := by
  induction p using Quotient.ind
  induction p' using Quotient.ind
  induction q, q' using Quotient.inductionOn₂
  exact Program.seq_mono hp hq

end Arrow

/-- The category of native typed programs modulo mutual handled-trace inclusion.
The unit and associativity laws follow from the ITree bind laws. -/
instance : Category (Interface M policy) where
  Hom := Arrow
  id A := Quotient.mk _ (Program.id A.ty)
  comp := Arrow.seq
  id_comp f := by exact Quotient.inductionOn f (fun p => Quotient.sound (Proofs.id_seq p))
  comp_id f := by exact Quotient.inductionOn f (fun p => Quotient.sound (Proofs.seq_id p))
  assoc f g h := by
    exact Quotient.inductionOn₃ f g h (fun p q r => Quotient.sound (Proofs.seq_assoc p q r))

instance (A B : Interface M policy) : PartialOrder (A ⟶ B) where
  le := Arrow.le
  le_refl := by exact Proofs.le_refl
  le_trans := by exact fun _ _ _ => Proofs.le_trans
  le_antisymm := by exact fun _ _ => Proofs.le_antisymm

/-- The homs are posets and categorical composition is monotone jointly. -/
instance : OrderedCategory (Interface M policy) where
  comp_mono := Arrow.seq_mono

namespace Arrow

variable {A B : Interface M policy}

/-- Take the observational class of a native program. -/
def ofProgram (p : Program Φ A.ty B.ty) : A ⟶ B :=
  Quotient.mk _ p

/-- The order on classes is the exact observation order on representatives. -/
@[simp] theorem ofProgram_le_ofProgram {p q : Program Φ A.ty B.ty} :
    ofProgram (A := A) (B := B) p ≤ ofProgram q ↔
      Program.Refines M policy p q :=
  Iff.rfl

/-- Class equality records mutual inclusion of the actual native runs. -/
theorem ofProgram_eq_iff {p q : Program Φ A.ty B.ty} :
    ofProgram (A := A) (B := B) p = ofProgram (A := A) (B := B) q ↔
      Program.Refines M policy p q ∧ Program.Refines M policy q p :=
  ⟨Quotient.exact, Quotient.sound (s := Program.setoid M policy A.ty B.ty)⟩

end Arrow

/-- Categorical composition uses actual native sequencing on representatives. -/
@[simp] theorem ofProgram_comp {A B C : Interface M policy} (p : Program Φ A.ty B.ty)
    (q : Program Φ B.ty C.ty) :
    Arrow.ofProgram (A := A) (B := B) p ≫ Arrow.ofProgram (A := B) (B := C) q =
      Arrow.ofProgram (p.seq q) :=
  rfl

/-- The joint composition operation as a map of hom posets. -/
def compOrderHom (A B C : Interface M policy) : ((A ⟶ B) × (B ⟶ C)) →o (A ⟶ C) where
  toFun f := f.1 ≫ f.2
  monotone' := fun _ _ h => Arrow.seq_mono h.1 h.2

end Silmaril.Isotope.LetCase.HandledTrace
