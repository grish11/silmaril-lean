module

public import Silmaril.Logic.Algebraic.Initial.Matching.FiniteSorted.Expansion.Defs

set_option backward.isDefEq.respectTransparency false

/-! Source SAT/UNSAT and consequence reflection use actual guarded expansion,
proved equational model-iso invariance and the full freeness constraint semantics.
All original equation contexts, finite profiles and ambient maps are retained. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution
open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Matching
open Silmaril.Logic.Institution.Structured

private theorem term_eval_hom {B : EQ.Signature} {M N : EQ.Algebra B}
    (f : M ⟶ N) {k : Nat} {Γ : Fin k → B.S} {s : B.S}
    (t : EQ.Term B Γ s) (v : ∀ i, M.carrier (Γ i)) :
    f.map s (t.eval M v) = t.eval N (fun i => f.map (Γ i) (v i)) := by
  induction t with
  | var => rfl
  | app op args ih =>
      change f.map _ (M.op op _) = N.op op _
      rw [f.map_op]
      exact congrArg (N.op op) (funext ih)

private def algebraCarrierEquiv {B : EQ.Signature} {M N : EQ.Algebra B}
    (e : M ≅ N) (s : B.S) : M.carrier s ≃ N.carrier s where
  toFun := e.hom.map s
  invFun := e.inv.map s
  left_inv x := congrArg (fun f : M ⟶ M => f.map s x) e.hom_inv_id
  right_inv x := congrArg (fun f : N ⟶ N => f.map s x) e.inv_hom_id

private theorem equation_holds_of_iso {B : EQ.Signature} {M N : EQ.Algebra B}
    (e : M ≅ N) (q : EQ.Equation B) (h : q.Holds M) : q.Holds N := by
  intro v
  let w : ∀ i, M.carrier (q.ctx i) := fun i => e.inv.map _ (v i)
  have hv : (fun i => e.hom.map (q.ctx i) (w i)) = v :=
    funext (fun i => (algebraCarrierEquiv e (q.ctx i)).right_inv (v i))
  have hh := congrArg (e.hom.map q.sort) (h w)
  have he := (term_eval_hom e.hom q.lhs w).symm.trans
    (hh.trans (term_eval_hom e.hom q.rhs w))
  simpa only [hv] using he

/-- Complete original variable contexts are transported through the actual iso;
empty carriers and unused context variables are retained. -/
theorem equation_holds_iso {B : EQ.Signature} {M N : EQ.Algebra B}
    (e : M ≅ N) (q : EQ.Equation B) : q.Holds M ↔ q.Holds N :=
  ⟨equation_holds_of_iso e q, equation_holds_of_iso e.symm q⟩

/-- Proved base-room invariance, rather than an assumed property of constraints. -/
theorem equationalRoom_isoInvariant (B : EQ.Signature) :
    (Initial.equational.obj B).IsoInvariant := by
  intro M N h q
  obtain ⟨e⟩ := h
  exact equation_holds_iso e q.down

/-- The actual freeness constraint includes target-modelhood after reduct. -/
theorem Sentence.satisfies_iso {B : EQ.Signature} {M N : EQ.Algebra B}
    (e : M ≅ N) (p : Sentence B) : p.Satisfies M ↔ p.Satisfies N :=
  Constraints.sat_iso Initial.equational e p.actual
    (equationalRoom_isoInvariant p.actual.target.sig)

theorem sourceRoom_isoInvariant (B : EQ.Signature) : (sourceRoom B).IsoInvariant := by
  intro M N h p
  obtain ⟨e⟩ := h
  exact Sentence.satisfies_iso e p

/-- The chosen guarded expansions retain all source objects and all actual
source homomorphisms, with their composition laws. -/
def expandModels (B : EQ.Signature) : EQ.Algebra B ⥤ SignedSpectrum.NativeModel B where
  obj := expandModel
  map := expandHom
  map_id M := by
    apply (decodeModels_faithful B (expandModel M) (expandModel M))
    change (decodeExpandIso M).hom ≫ 𝟙 M ≫ (decodeExpandIso M).inv = 𝟙 _
    simp only [Category.id_comp, Iso.hom_inv_id]
  map_comp {M N P} h k := by
    apply (decodeModels_faithful B (expandModel M) (expandModel P))
    change (decodeExpandIso M).hom ≫ (h ≫ k) ≫ (decodeExpandIso P).inv =
      ((decodeExpandIso M).hom ≫ h ≫ (decodeExpandIso N).inv) ≫
        ((decodeExpandIso N).hom ≫ k ≫ (decodeExpandIso P).inv)
    simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- A natural isomorphism of full model functors, not literal object equality. -/
def expansionDecodeIso (B : EQ.Signature) :
    expandModels B ⋙ decodeModels B ≅ 𝟭 (EQ.Algebra B) :=
  NatIso.ofComponents decodeExpandIso (by
    intro M N h
    change ((decodeExpandIso M).hom ≫ h ≫ (decodeExpandIso N).inv) ≫
      (decodeExpandIso N).hom = (decodeExpandIso M).hom ≫ h
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

theorem comparison_isoExpansive (B : EQ.Signature) : Corridor.IsoExpansive (comparison B) :=
  fun M => ⟨expandModel M, ⟨decodeExpandIso M⟩⟩

theorem comparison_elemExpansive (B : EQ.Signature) : Corridor.ElemExpansive (comparison B) :=
  Corridor.IsoExpansive.elemExpansive (sourceRoom_isoInvariant B) (comparison_isoExpansive B)

theorem toMatching_elemExpansive : toMatching.ElemExpansive := by
  intro B
  exact comparison_elemExpansive B

theorem toMatching_faithful : toMatching.Faithful :=
  Inst.CoHom.ElemExpansive.faithful toMatching_elemExpansive

/-- One chosen actual guarded expansion satisfies precisely the original
finite-presentation sentences true in its source algebra. -/
theorem expandModel_satisfaction {B : EQ.Signature} (M : EQ.Algebra B) (p : Sentence B) :
    (theoryRoom B).Sat (expandModel M) p.compile ↔ p.Satisfies M :=
  (Sentence.compile_satisfaction (expandModel M) p).trans
    (Sentence.satisfies_iso (decodeExpandIso M) p)

/-- Arbitrary source theories may mix finite original profiles, equations and
contexts in the same ambient signature. No target image modelhood is assumed. -/
theorem satisfiable_compile_iff {B : EQ.Signature} (H : Set (Sentence B)) :
    SourceSatisfiable H ↔ TargetSatisfiable (Sentence.compile '' H) := by
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨expandModel M, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    exact (expandModel_satisfaction M p).mpr (hM p hp)
  · rintro ⟨N, hN⟩
    refine ⟨SignedSpectrum.decode N, ?_⟩
    intro p hp
    exact (Sentence.compile_satisfaction N p).mp (hN _ ⟨p, hp, rfl⟩)

theorem unsatisfiable_compile_iff {B : EQ.Signature} (H : Set (Sentence B)) :
    ¬ SourceSatisfiable H ↔ ¬ TargetSatisfiable (Sentence.compile '' H) :=
  not_congr (satisfiable_compile_iff H)

/-- Semantic consequence reflects through expansion up to actual algebra iso,
in addition to the original forward comparison theorem. -/
theorem entails_compile_iff {B : EQ.Signature} (H : Set (Sentence B)) (p : Sentence B) :
    (sourceRoom B).Entails H p ↔
      (theoryRoom B).Entails (Sentence.compile '' H) p.compile :=
  Corridor.entails_map_iff_of_elemExpansive (comparison_elemExpansive B) H p

theorem entails_reflect {B : EQ.Signature} (H : Set (Sentence B)) (p : Sentence B)
    (h : (theoryRoom B).Entails (Sentence.compile '' H) p.compile) :
    (sourceRoom B).Entails H p :=
  (entails_compile_iff H p).mpr h

end Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution
