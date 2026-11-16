module

public import Silmaril.Logic.Separation.Parameterized.FirstOrder.Compiler.Defs
public import Silmaril.Logic.FirstOrderLFP.Thms

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Separation.Parameterized.FirstOrder
open Silmaril.Logic.Institution.Examples

/-- Typed object-environment extension, including empty value carriers. -/
def extendEnv {S : FOL.Signature} (M : FOL.Structure S) {k} {Γ : Fin k → S.S}
    (s : S.S) (x : M.carrier s) (θ : ∀ i, M.carrier (Γ i)) :
    ∀ i, M.carrier (contextCons s Γ i) :=
  Fin.cases x θ

theorem holds_forallFormula {A : Signature} (M : Model A) {k} {Γ : Fin k → TargetSort}
    (s : TargetSort) (p : FOL.Formula (signature A) (Fin.cases s Γ))
    (θ : Silmaril.Logic.FirstOrderLFP.ObjEnv (model M) Γ) :
    (forallFormula s p).Holds (model M).toStructure θ ↔
      ∀ x, p.Holds (model M).toStructure (extendEnv (model M).toStructure s x θ) := by
  constructor
  · intro h x
    exact h (extendEnv (model M).toStructure s x θ) (fun _ => HEq.rfl)
  · intro h θ' hθ
    have heq : θ' = extendEnv (model M).toStructure s (θ' 0) θ := by
      funext i
      exact Fin.cases rfl (fun j => eq_of_heq (hθ j)) i
    rw [heq]
    exact h (θ' 0)

theorem holds_existsFormula {A : Signature} (M : Model A) {k} {Γ : Fin k → TargetSort}
    (s : TargetSort) (p : FOL.Formula (signature A) (Fin.cases s Γ))
    (θ : Silmaril.Logic.FirstOrderLFP.ObjEnv (model M) Γ) :
    (existsFormula s p).Holds (model M).toStructure θ ↔
      ∃ x, p.Holds (model M).toStructure (extendEnv (model M).toStructure s x θ) := by
  classical
  change (¬ (forallFormula s (.not p)).Holds (model M).toStructure θ) ↔ _
  rw [holds_forallFormula]
  simp only [FOL.Formula.Holds,not_forall,not_not]

theorem holds_impliesFormula {A : Signature} (M : Model A) {k} {Γ : Fin k → TargetSort}
    (p q : FOL.Formula (signature A) Γ)
    (θ : Silmaril.Logic.FirstOrderLFP.ObjEnv (model M) Γ) :
    (impliesFormula p q).Holds (model M).toStructure θ ↔
      (p.Holds (model M).toStructure θ → q.Holds (model M).toStructure θ) := by
  classical
  exact not_and_not_right

theorem holds_joinFormula {A : Signature} (M : Model A) {k} {Γ : Fin k → TargetSort}
    (a b c : TargetTerm A Γ .heap) (θ : Silmaril.Logic.FirstOrderLFP.ObjEnv (model M) Γ) :
    (joinFormula a b c).Holds (model M).toStructure θ ↔
      M.resource.join (a.eval (model M).toStructure.toAlgebra θ)
        (b.eval (model M).toStructure.toAlgebra θ) (c.eval (model M).toStructure.toAlgebra θ) := Iff.rfl

theorem holds_ownershipFormula {A : Signature} (M : Model A) {k n} {Γ : Fin k → TargetSort}
    (a : A.Atom n) (args : Fin n → TargetTerm A Γ .value) (h : TargetTerm A Γ .heap)
    (θ : Silmaril.Logic.FirstOrderLFP.ObjEnv (model M) Γ) :
    (ownershipFormula a args h).Holds (model M).toStructure θ ↔
      h.eval (model M).toStructure.toAlgebra θ ∈
        M.atom a (fun i => (args i).eval (model M).toStructure.toAlgebra θ) := Iff.rfl

theorem eval_liftHeap {A : Signature} (M : Model A) {k} {Γ : Fin k → TargetSort}
    {s} (u : TargetTerm A Γ s) (x : M.resource.carrier)
    (θ : Silmaril.Logic.FirstOrderLFP.ObjEnv (model M) Γ) :
    (liftHeap u).eval (model M).toStructure.toAlgebra
        (extendEnv (model M).toStructure .heap x θ) =
      u.eval (model M).toStructure.toAlgebra θ := by
  exact eval_liftTerm (model M).toStructure.toAlgebra TargetSort.heap u x θ

/-- Uniform semantic preservation for arbitrary target contexts, value-term
substitutions and current-heap terms. No source meaning is defined by compiling. -/
theorem assertion_correct {A : Signature} (M : Model A) {k} (p : Assertion A k)
    {l} {Γ : Fin l → TargetSort} (σ : Fin k → TargetTerm A Γ .value)
    (h : TargetTerm A Γ .heap) (θ : Silmaril.Logic.FirstOrderLFP.ObjEnv (model M) Γ) :
    (assertion p σ h).Holds (model M).toStructure θ ↔
      h.eval (model M).toStructure.toAlgebra θ ∈
        p.denote M (fun i => (σ i).eval (model M).toStructure.toAlgebra θ) := by
  induction p generalizing l with
  | eq t u =>
      simp only [assertion,FOL.Formula.Holds,eval_term,Assertion.denote]
      rfl
  | atom a args =>
      simp only [assertion,holds_ownershipFormula,eval_term,Assertion.denote]
  | emp => rfl
  | neg p ih =>
      simp only [assertion,FOL.Formula.Holds,ih,Assertion.denote,Set.mem_compl_iff]
  | conj p q hp hq =>
      simp only [assertion,FOL.Formula.Holds,hp,hq,Assertion.denote,Set.mem_inter_iff]
  | sep p q hp hq =>
      simp only [assertion,holds_existsFormula,FOL.Formula.Holds,holds_joinFormula,hp,hq,
        Assertion.denote,Separation.Resource.sep,
        eval_liftHeap,EQ.Term.eval]
      rfl
  | wand p q hp hq =>
      simp only [assertion,holds_forallFormula,holds_impliesFormula,holds_joinFormula,hp,hq,
        Assertion.denote,Separation.Resource.wand,
        eval_liftHeap,EQ.Term.eval]
      rfl

theorem eval_castTerm {S : EQ.Signature} (M : EQ.Algebra S) {k} {Γ : Fin k → S.S}
    {s t : S.S} (e : s = t) (u : EQ.Term S Γ s) (θ : ∀ i, M.carrier (Γ i)) :
    HEq ((Eq.mp (congrArg (EQ.Term S Γ) e) u).eval M θ) (u.eval M θ) := by
  cases e
  rfl

theorem eval_tupleHeap {A : Signature} (M : Model A) {n l} {Γ : Fin l → TargetSort}
    (θ : Silmaril.Logic.FirstOrderLFP.ObjEnv (model M) (tupleContext n Γ))
    (x : Silmaril.Logic.FirstOrderLFP.Tuple (model M) (profile A n))
    (ρ : Silmaril.Logic.FirstOrderLFP.ObjEnv (model M) Γ)
    (hθ : Silmaril.Logic.FirstOrderLFP.Extends θ x ρ) :
    (tupleHeap n Γ).eval (model M).toStructure.toAlgebra θ = x 0 := by
  exact eq_of_heq ((eval_castTerm _ (by simp [tupleContext,pointerHeapTargetSorts])
    (.var ((0 : Fin (n+1)).castAdd l)) θ).trans (hθ.1 0))

theorem eval_tupleValue {A : Signature} (M : Model A) {n l} {Γ : Fin l → TargetSort}
    (θ : Silmaril.Logic.FirstOrderLFP.ObjEnv (model M) (tupleContext n Γ))
    (x : Silmaril.Logic.FirstOrderLFP.Tuple (model M) (profile A n))
    (ρ : Silmaril.Logic.FirstOrderLFP.ObjEnv (model M) Γ)
    (hθ : Silmaril.Logic.FirstOrderLFP.Extends θ x ρ) (j : Fin n) :
    (tupleValue n Γ j).eval (model M).toStructure.toAlgebra θ = x j.succ := by
  exact eq_of_heq ((eval_castTerm _ (by simp [tupleContext,pointerHeapTargetSorts])
    (.var (j.succ.castAdd l)) θ).trans (hθ.1 j.succ))

theorem eval_tupleAmbientVar {A : Signature} (M : Model A) {n l} {Γ : Fin l → TargetSort}
    (θ : Silmaril.Logic.FirstOrderLFP.ObjEnv (model M) (tupleContext n Γ))
    (x : Silmaril.Logic.FirstOrderLFP.Tuple (model M) (profile A n))
    (ρ : Silmaril.Logic.FirstOrderLFP.ObjEnv (model M) Γ)
    (hθ : Silmaril.Logic.FirstOrderLFP.Extends θ x ρ) (i : Fin l) :
    (tupleAmbientVar n Γ i).eval (model M).toStructure.toAlgebra θ = ρ i := by
  exact eq_of_heq ((eval_castTerm _ (by simp [tupleContext])
    (.var (Fin.natAdd (n+1) i)) θ).trans (hθ.2 i))

theorem eval_bodyValues {A : Signature} (M : Model A) {n k l} {Γ : Fin l → TargetSort}
    (σ : Fin k → TargetTerm A Γ .value)
    (θ : Silmaril.Logic.FirstOrderLFP.ObjEnv (model M) (tupleContext n Γ))
    (x : Silmaril.Logic.FirstOrderLFP.Tuple (model M) (profile A n))
    (ρ : Silmaril.Logic.FirstOrderLFP.ObjEnv (model M) Γ)
    (hθ : Silmaril.Logic.FirstOrderLFP.Extends θ x ρ) :
    (fun i => (bodyValues n σ i).eval (model M).toStructure.toAlgebra θ) =
      appendValues M (fun j => x j.succ) (fun i => (σ i).eval (model M).toStructure.toAlgebra ρ) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa only [bodyValues,appendValues,Fin.addCases_left] using eval_tupleValue M θ x ρ hθ j
  · intro j
    simp only [bodyValues,appendValues,Fin.addCases_right,eval_substitute]
    have he : (fun i => (tupleAmbientVar n Γ i).eval (model M).toStructure.toAlgebra θ) = ρ :=
      funext (eval_tupleAmbientVar M θ x ρ hθ)
    rw [he]

/-- A bijection conjugates actual powerset least fixed points. The body
hypothesis concerns every relation, never a finite unfolding approximation. -/
theorem lfp_conjugate {α β : Type} (e : α ≃ β) (F : Set α →o Set α) (G : Set β →o Set β)
    (h : ∀ Y y, y ∈ G Y ↔ e.symm y ∈ F {x | e x ∈ Y}) :
    G.lfp = {y | e.symm y ∈ F.lfp} := by
  apply le_antisymm
  · apply G.lfp_le
    intro y hy
    have hx := (h _ y).mp hy
    have he : {x | e x ∈ {y | e.symm y ∈ F.lfp}} = F.lfp := by
      ext x
      simp only [Set.mem_ofPred_eq,e.symm_apply_apply]
    rw [he,F.map_lfp] at hx
    exact hx
  · have hp : F {x | e x ∈ G.lfp} ⊆ {x | e x ∈ G.lfp} := by
      intro x hx
      have hy := (h G.lfp (e x)).mpr (by simpa only [e.symm_apply_apply] using hx)
      rw [G.map_lfp] at hy
      exact hy
    intro y hy
    have hx := F.lfp_le hp hy
    simpa only [Set.mem_ofPred_eq,e.apply_symm_apply] using hx

theorem insert_encode {A : Signature} (M : Model A) {r} (P' : Fin (r+1) → Nat)
    (η : RelEnv M (P' ∘ Fin.succ))
    (Y : Set (Silmaril.Logic.FirstOrderLFP.Tuple (model M) (profile A (P' 0)))) :
    encodeRelEnv M (insert M P' η {s | encodeState M s ∈ Y}) =
      Silmaril.Logic.FirstOrderLFP.insertRel (model M) (fun i => profile A (P' i)) (encodeRelEnv M η) Y := by
  funext i
  refine Fin.cases ?_ (fun _ => rfl) i
  ext x
  change encodeState M (decodeState M x) ∈ Y ↔ x ∈ Y
  change (stateEquiv M (P' 0)) ((stateEquiv M (P' 0)).symm x) ∈ Y ↔ x ∈ Y
  rw [(stateEquiv M (P' 0)).apply_symm_apply]

theorem eval_liftValue {A : Signature} (M : Model A) {k} {Γ : Fin k → TargetSort}
    {s} (u : TargetTerm A Γ s) (x : M.Value)
    (θ : Silmaril.Logic.FirstOrderLFP.ObjEnv (model M) Γ) :
    (liftTerm (S := (signature A).toSignature) TargetSort.value u).eval (model M).toStructure.toAlgebra
        (extendEnv (model M).toStructure .value x θ) =
      u.eval (model M).toStructure.toAlgebra θ := by
  exact eval_liftTerm (model M).toStructure.toAlgebra TargetSort.value u x θ

theorem eval_boundValues {A : Signature} (M : Model A) {k l} {Γ : Fin l → TargetSort}
    (σ : Fin k → TargetTerm A Γ .value) (x : M.Value)
    (θ : Silmaril.Logic.FirstOrderLFP.ObjEnv (model M) Γ) :
    (fun i => (boundValues σ i).eval (model M).toStructure.toAlgebra
      (extendEnv (model M).toStructure .value x θ)) =
      consValues M x (fun i => (σ i).eval (model M).toStructure.toAlgebra θ) := by
  funext i
  refine Fin.cases rfl ?_ i
  intro j
  exact eval_liftValue M (σ j) x θ

end Silmaril.Logic.Separation.Parameterized.FirstOrder
