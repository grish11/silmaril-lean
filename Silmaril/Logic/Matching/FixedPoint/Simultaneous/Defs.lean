module

public import Silmaril.Logic.Matching.FixedPoint.Variables.Thms
public import Silmaril.Logic.Matching.SortMaps.Thms
public import Silmaril.Logic.ModalMu.FiniteVector.Thms

/-! Finite dependent blocks over the existing many-sorted native unary μ syntax.
The simultaneous semantics is an independent product-lattice least fixed point.
Neither carriers nor coordinates are identified when their sorts coincide. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.FixedPoint.Simultaneous
open CategoryTheory
open Algebraic.ManySorted (Signature)
open Silmaril.Logic.ModalMu
variable {S : Type} {A : Signature S}

abbrev append {r l : Nat} (P : Fin r → S) (Q : Fin l → S) : Fin (r+l) → S :=
  Fin.addCases P Q

structure System (A : Signature S) {r l k : Nat}
    (P : Fin r → S) (Q : Fin l → S) (Γ : Fin k → S) where
  body : ∀ i, Pattern A (append P Q) Γ (P i)

theorem append_left {r l : Nat} (P : Fin r → S) (Q : Fin l → S) (i : Fin r) :
    append P Q (Fin.castAdd l i) = P i := Fin.addCases_left i

theorem append_right {r l : Nat} (P : Fin r → S) (Q : Fin l → S) (i : Fin l) :
    append P Q (Fin.natAdd r i) = Q i := Fin.addCases_right i

private theorem cast_subset {D : S → Type} {s t : S} (h : s = t)
    {X Y : Set (D s)} (hXY : X ⊆ Y) : (h ▸ X : Set (D t)) ⊆ (h ▸ Y) := by
  cases h
  exact hXY

def joinEnv (M : Model A) {r l : Nat} {P : Fin r → S} {Q : Fin l → S}
    (η : SetEnv A M Q) (X : SetEnv A M P) : SetEnv A M (append P Q) :=
  Fin.addCases
    (fun i => (append_left P Q i).symm ▸ X i)
    (fun i => (append_right P Q i).symm ▸ η i)

def System.operator {r l k : Nat} {P : Fin r → S} {Q : Fin l → S}
    {Γ : Fin k → S} (s : System A P Q Γ) (M : Model A) (v : ObjEnv A M Γ)
    (η : SetEnv A M Q) : SetEnv A M P →o SetEnv A M P where
  toFun X i := (s.body i).denote M v (joinEnv M η X)
  monotone' := by
    intro X Y h i
    apply (s.body i).denote M v |>.monotone
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [joinEnv, Fin.addCases_left]
      exact cast_subset _ (h i)
    · simp only [joinEnv, Fin.addCases_right]
      exact le_rfl

def System.denote {r l k : Nat} {P : Fin r → S} {Q : Fin l → S}
    {Γ : Fin k → S} (s : System A P Q Γ) (M : Model A) (v : ObjEnv A M Γ)
    (η : SetEnv A M Q) : SetEnv A M P :=
  (s.operator M v η).lfp

def splitEnv (M : Model A) {r : Nat} (P : Fin (r+1) → S) :
    SetEnv A M P ≃o (Set (M.carrier (P 0)) × SetEnv A M (P ∘ Fin.succ)) where
  toFun X := (X 0, fun i => X i.succ)
  invFun X := Fin.cases X.1 X.2
  left_inv X := by funext i; exact Fin.cases rfl (fun _ => rfl) i
  right_inv X := by cases X; rfl
  map_rel_iff' := by
    intro X Y
    constructor
    · intro h i; exact Fin.cases h.1 h.2 i
    · intro h; exact ⟨h 0, fun i => h i.succ⟩

/-- Reorder the head equation into the first captured slot, preserving each sort. -/
def tailRen {r l : Nat} (P : Fin (r+1) → S) (Q : Fin l → S) :
    Ren (append P Q) (append (P ∘ Fin.succ) (Fin.cases (P 0) Q)) :=
  fun i => Fin.addCases
    (Fin.cases
      ⟨Fin.natAdd r 0, by simp [append]⟩
      (fun j => ⟨Fin.castAdd (l+1) j, by simp [append]⟩))
    (fun j => ⟨Fin.natAdd r j.succ, by simp [append]⟩) i

def System.tail {r l k : Nat} {P : Fin (r+1) → S} {Q : Fin l → S}
    {Γ : Fin k → S} (s : System A P Q Γ) :
    System A (P ∘ Fin.succ) (Fin.cases (P 0) Q) Γ :=
  ⟨fun i => (s.body i.succ).renameSets (tailRen P Q)⟩

def headSub {r l k : Nat} {P : Fin (r+1) → S} {Q : Fin l → S}
    {Γ : Fin k → S}
    (tail : ∀ i : Fin r, Pattern A (Fin.cases (P 0) Q) Γ (P i.succ)) :
    ∀ i, Pattern A (Fin.cases (P 0) Q) Γ (append P Q i) :=
  Fin.addCases
    (fun i => (append_left P Q i).symm ▸ Fin.cases (.setvar 0) tail i)
    (fun i => (append_right P Q i).symm ▸ Pattern.setvar i.succ)

/-- Dependent Bekič elimination into actual unary μ patterns.
Distinct source coordinates survive even when their sorts are equal. -/
def System.compile :
    {r l k : Nat} → {P : Fin r → S} → {Q : Fin l → S} →
    {Γ : Fin k → S} → System A P Q Γ → ∀ i, Pattern A Q Γ (P i)
  | 0, _, _, _, _, _, _ => fun i => i.elim0
  | _r+1, _l, _k, P, Q, Γ, s =>
      let tail := s.tail.compile
      let head : Pattern A Q Γ (P 0) :=
        Pattern.mu (P' := Fin.cases (P 0) Q)
          ((s.body 0).substituteSets (Q := Fin.cases (P 0) Q) (headSub tail))
      Fin.cases head (fun i => (tail i).substituteSets (Fin.cases head Pattern.setvar))

theorem map_append {B C : SortMaps.Signature} (f : B ⟶ C)
    {r l : Nat} (P : Fin r → B.sorts) (Q : Fin l → B.sorts) :
    f.sorts ∘ append P Q = append (f.sorts ∘ P) (f.sorts ∘ Q) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [append]

/-- Mapping changes sorts and symbols, retaining the full source coordinate family. -/
def System.map {B C : SortMaps.Signature} (f : B ⟶ C)
    {r l k : Nat} {P : Fin r → B.sorts} {Q : Fin l → B.sorts}
    {Γ : Fin k → B.sorts} (s : System B.symbols P Q Γ) :
    System C.symbols (f.sorts ∘ P) (f.sorts ∘ Q) (f.sorts ∘ Γ) :=
  ⟨fun i => (map_append f P Q) ▸ SortMaps.Hom.fixedPattern f (s.body i)⟩

end Silmaril.Logic.Matching.FixedPoint.Simultaneous
