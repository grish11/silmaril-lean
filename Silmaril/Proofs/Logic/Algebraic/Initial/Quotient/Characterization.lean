module

public import Silmaril.Logic.Algebraic.Initial.Quotient.Characterization.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Initial.Presented.Characterization
open CategoryTheory CategoryTheory.Limits Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Institution.Structured

/-- Generatedness supplies complete valuations, even for unused variables. -/
theorem models_of_generated_kernel {T : Theory} (A : EQ.Algebra T.sig)
    (generated : Generated A) (kernel : ExactGroundKernel T A) :
    ∀ e ∈ T.axioms, e.down.Holds A := by
  classical
  intro lifted member valuation
  let e := lifted.down
  let terms : (i : Fin e.k) → Ground T.sig (e.ctx i) :=
    fun i => Classical.choose (generated (e.ctx i) (valuation i))
  have values : (fun i => evaluate A (terms i)) = valuation := by
    funext i
    exact Classical.choose_spec (generated (e.ctx i) (valuation i))
  have relation := Rel.equation (T := T) (Γ := closedContext T.sig) e member terms
  have equality := (kernel e.sort _ _).2 relation
  have left := eval_hom (Initial.foldHom A (fun i => i.elim0)) terms e.lhs
  have right := eval_hom (Initial.foldHom A (fun i => i.elim0)) terms e.rhs
  have result := left.symm.trans (equality.trans right)
  change e.lhs.eval A (fun i => evaluate A (terms i)) =
    e.rhs.eval A (fun i => evaluate A (terms i)) at result
  rw [values] at result
  exact result

/-- Exact kernel and generation make the existing quotient evaluation bijective. -/
theorem fold_bijective {T : Theory} (M : Models T)
    (generated : Generated M.obj) (kernel : ExactGroundKernel T M.obj) (s : T.sig.S) :
    Function.Bijective ((Presented.foldHom (Γ := closedContext T.sig) M (fun i => i.elim0)).map s) := by
  constructor
  · intro a b equality
    induction a using Quotient.inductionOn with
    | h a =>
      induction b using Quotient.inductionOn with
      | h b =>
        exact Quotient.sound ((kernel s a b).1 equality)
  · intro value
    obtain ⟨term, hterm⟩ := generated s value
    exact ⟨Quotient.mk _ term, hterm⟩

/-- The inverse is an actual algebra homomorphism in the original all-hom model
category, rather than a replacement model category with equality arrows. -/
def foldIso {T : Theory} (M : Models T)
    (generated : Generated M.obj) (kernel : ExactGroundKernel T M.obj) :
    quotientModel T ≅ M := by
  let f := Presented.foldHom (Γ := closedContext T.sig) M (fun i => i.elim0)
  let e : (s : T.sig.S) → (quotientModel T).obj.carrier s ≃ M.obj.carrier s :=
    fun s => Equiv.ofBijective (f.map s) (fold_bijective M generated kernel s)
  let inverse : M.obj ⟶ (quotientModel T).obj :=
    { map := fun s => (e s).symm
      map_op := by
        intro n w s op args
        apply (e s).injective
        calc
          e s ((e s).symm (M.obj.op op args)) = M.obj.op op args :=
            (e s).apply_symm_apply _
          _ = M.obj.op op (fun i => f.map (w i) ((e (w i)).symm (args i))) := by
            apply congrArg (M.obj.op op)
            funext i
            exact ((e (w i)).apply_symm_apply (args i)).symm
          _ = e s ((quotientModel T).obj.op op (fun i => (e (w i)).symm (args i))) :=
            (f.map_op op (fun i => (e (w i)).symm (args i))).symm }
  refine ⟨⟨f⟩, ⟨inverse⟩, ?_, ?_⟩
  · apply ObjectProperty.hom_ext
    apply algebraHom_ext
    funext s x
    exact (e s).symm_apply_apply x
  · apply ObjectProperty.hom_ext
    apply algebraHom_ext
    funext s x
    exact (e s).apply_symm_apply x

/-- Actual theory-model isomorphisms have bijective underlying sorted maps. -/
theorem iso_map_bijective {T : Theory} {M N : Models T} (e : M ≅ N) (s : T.sig.S) :
    Function.Bijective (e.hom.hom.map s) := by
  have left (x : M.obj.carrier s) : e.inv.hom.map s (e.hom.hom.map s x) = x :=
    congrArg (fun f : M ⟶ M => f.hom.map s x) e.hom_inv_id
  have right (x : N.obj.carrier s) : e.hom.hom.map s (e.inv.hom.map s x) = x :=
    congrArg (fun f : N ⟶ N => f.hom.map s x) e.inv_hom_id
  exact ⟨fun x y h => (left x).symm.trans ((congrArg (e.inv.hom.map s) h).trans (left _)),
    fun x => ⟨e.inv.hom.map s x, right x⟩⟩

/-- Independent initiality implies exactly the two ground-term properties. -/
theorem generated_kernel_of_initial {T : Theory} (M : Models T) (initial : IsInitial M) :
    Generated M.obj ∧ ExactGroundKernel T M.obj := by
  let e := (quotientModel_isInitial T).uniqueUpToIso initial
  have same : e.hom = (⟨Presented.foldHom (Γ := closedContext T.sig) M (fun i => i.elim0)⟩ : quotientModel T ⟶ M) :=
    (quotientModel_isInitial T).hom_ext _ _
  have bijective (s : T.sig.S) :
      Function.Bijective ((Presented.foldHom (Γ := closedContext T.sig) M (fun i => i.elim0)).map s) := by
    have result := iso_map_bijective e s
    rw [same] at result
    change Function.Bijective
      ((Presented.foldHom (Γ := closedContext T.sig) M (fun i => i.elim0)).map s) at result
    exact result
  constructor
  · intro s x
    obtain ⟨q, hq⟩ := (bijective s).2 x
    induction q using Quotient.inductionOn with
    | h term => exact ⟨term, hq⟩
  · intro s a b
    constructor
    · intro equality
      have equal_classes : Quotient.mk (Presented.setoid T (closedContext T.sig) s) a =
          Quotient.mk (Presented.setoid T (closedContext T.sig) s) b :=
        (bijective s).1 equality
      exact Quotient.exact equal_classes
    · intro relation
      exact rel_sound M (fun i => i.elim0) relation

/-- Characterization in the genuine existing quotient/all-hom model category. -/
theorem initial_iff_generated_kernel {T : Theory} (M : Models T) :
    Nonempty (IsInitial M) ↔ Generated M.obj ∧ ExactGroundKernel T M.obj := by
  constructor
  · rintro ⟨initial⟩
    exact generated_kernel_of_initial M initial
  · rintro ⟨generated, kernel⟩
    exact ⟨(quotientModel_isInitial T).ofIso (foldIso M generated kernel)⟩

/-- No hidden modelhood assumption: the ground properties recover all original
axioms before constructing the actual initial object. -/
theorem modelhood_initial_iff {T : Theory} (A : EQ.Algebra T.sig) :
    (∃ h : ∀ e ∈ T.axioms, e.down.Holds A,
      Nonempty (IsInitial (⟨A, h⟩ : Models T))) ↔
      Generated A ∧ ExactGroundKernel T A := by
  constructor
  · rintro ⟨h, initial⟩
    exact (initial_iff_generated_kernel (⟨A, h⟩ : Models T)).1 initial
  · rintro ⟨generated, kernel⟩
    exact ⟨models_of_generated_kernel A generated kernel,
      (initial_iff_generated_kernel _).2 ⟨generated, kernel⟩⟩

end Silmaril.Logic.Algebraic.Initial.Presented.Characterization
