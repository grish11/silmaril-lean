module

public import Silmaril.SSA.Isotope.Institution.Adapters.Powerset.Defs

@[expose] public section

namespace Silmaril.Isotope.Institution.Adapters.Powerset.Proofs

open CategoryTheory Semantics
open Silmaril.Logic.Metatheory.TheoryModel Silmaril.Logic.Institution
open Parallel (Tier CaseTypes Control ParOp Tm Derivation)
open Parallel.Institution

universe u v

variable {τ ε : Type u} {S T : InstrSig τ ε} {D : τ → Type v}
  {ν : Type u} [DecidableEq ν] {Γ : Ctx ν τ}

private theorem primitive_cast {A B C E : τ} (hs : A = B) (ht : C = E)
    (r : D A → D C → Prop) (a : D B) :
    ({b | r (cast (congrArg D hs.symm) a) (cast (congrArg D ht.symm) b)} : SetM (D E)) =
      (ht ▸ ({b | r (hs.symm ▸ a) b} : SetM (D C))) := by
  cases hs
  cases ht
  rfl

theorem parallel_reduct (f : S ⟶ T) (X : Model D T) (pair : ParOp (SetM : Type v → Type v)) :
    (X.reduct f).toParallel pair = (X.toParallel pair).reduct f := by
  let mkModel := fun (eval : (op : S.Instr) → D (instrSrc op) → SetM (D (instrTrg op))) =>
    { (X.reduct f).toParallel pair with instr := ⟨eval⟩ }
  apply congrArg mkModel
  funext op a
  exact primitive_cast (f.source op) (f.target op) (X.relational.eval (f.instr op)) a

theorem strict_arrow_iff (pair : ParOp (SetM : Type v → Type v)) (X Y : Model D S) :
    Nonempty (X ⟶ Y) ↔
      ∃ H : Parallel.Institution.Model.Hom (X.toParallel pair) (Y.toParallel pair),
        ∀ (A : Type v) (a : SetM A), H.app a = a := by
  constructor
  · rintro ⟨h⟩
    cases h.down
    exact ⟨𝟙 (X.toParallel pair), fun _ _ => rfl⟩
  · rintro ⟨H, identity⟩
    have e : X.relational.toSetModel = Y.relational.toSetModel := by
      apply congrArg (fun eval => (⟨eval⟩ : InstructionModel D S.Instr SetM))
      funext op x
      exact (identity _ _).symm.trans (H.map_instr op x)
    have r : X.relational = Y.relational := congrArg RelationModel.ofSetModel e
    exact ⟨⟨congrArg Model.mk r⟩⟩

theorem toParallelFunctor_reduct (f : S ⟶ T) (pair : ParOp (SetM : Type v → Type v)) :
    Model.reductFunctor f ⋙ Model.toParallelFunctor (D := D) pair =
      Model.toParallelFunctor pair ⋙ Parallel.Institution.Model.reductFunctor f := by
  let F := Model.reductFunctor f ⋙ Model.toParallelFunctor (D := D) pair
  let G := Model.toParallelFunctor (D := D) pair ⋙ Parallel.Institution.Model.reductFunctor f
  change F = G
  have objects (X : Model D T) : F.obj X = G.obj X := parallel_reduct f X pair
  refine CategoryTheory.Functor.ext objects ?_
  intro X Y h
  have e : X = Y := h.down
  subst Y
  have eh : h = 𝟙 X := Subsingleton.elim _ _
  subst h
  rw [F.map_id, G.map_id, Category.id_comp, eqToHom_trans, eqToHom_refl]

section Seq

variable [HasProduct τ] [HasUnit τ]
open Silmaril.Isotope.LetSeq.LocallyNameless in
private def seqMap (g : S ⟶ T) : {n : Nat} → {β : BoundCtx τ n} → {t : Tm ν S.Instr n} →
    {A : τ} → Derivation S.Instr Γ β t A → Derivation T.Instr Γ β (t.mapInstr g.instr) A
  | _, _, _, _, .fv h => .fv h
  | _, _, _, _, .bv => .bv
  | _, _, _, _, .op (f := f) a =>
      g.target f ▸ .op (f := g.instr f) ((g.source f).symm ▸ seqMap g a)
  | _, _, _, _, .let₁ a b => .let₁ (seqMap g a) (seqMap g b)
  | _, _, _, _, .unit => .unit
  | _, _, _, _, .pair a b => .pair (seqMap g a) (seqMap g b)
  | _, _, _, _, .let₂ a b => .let₂ (seqMap g a) (seqMap g b)

private abbrev seqFold (f : S ⟶ T) {k : Nat} {bound : BoundCtx τ k}
    {a : Silmaril.Isotope.LetSeq.LocallyNameless.Tm ν S.Instr k} {X : τ}
    (d : Silmaril.Isotope.LetSeq.LocallyNameless.Derivation S.Instr Γ bound a X) :
    Relational.LetSeq.Program T Γ ⟨k, bound, X⟩ :=
  Silmaril.Isotope.LetSeq.LocallyNameless.Models.denote
    (Algebra.reductObj (Silmaril.Isotope.Institution.LetSeq.sigHom Γ f)
      (Silmaril.Isotope.LetSeq.LocallyNameless.Models.syntaxAlgebra T.Instr Γ)) d

private theorem seqTranslate (f : S ⟶ T) {k : Nat} {bound : BoundCtx τ k}
    {a : Silmaril.Isotope.LetSeq.LocallyNameless.Tm ν S.Instr k} {X : τ}
    (d : Silmaril.Isotope.LetSeq.LocallyNameless.Derivation S.Instr Γ bound a X) :
    Relational.LetSeq.Program.translate f (i := ⟨k, bound, X⟩) ⟨a, d⟩ = ⟨a.mapInstr f.instr, seqMap f d⟩ := by
  refine (Relational.LetSeq.Program.translate_eq_fold f
    (i := ⟨k, bound, X⟩) ⟨a, d⟩).trans ?_
  change seqFold f d = _
  induction d with
  | fv | bv | unit => rfl
  | @op k bound op a d ih =>
      refine (Relational.LetSeq.Program.translate_eq_fold f
        (i := ⟨k, bound, instrTrg op⟩) ⟨.op op a, .op d⟩).symm.trans ?_
      refine (Relational.LetSeq.Program.translate_op f op ⟨a, d⟩).trans ?_
      erw [Relational.LetSeq.Program.translate_eq_fold f (i := ⟨k, bound, instrSrc op⟩) ⟨a, d⟩]
      change (⟨.op (f.instr op) (seqFold f d).1,
        f.target op ▸ .op ((f.source op).symm ▸ (seqFold f d).2)⟩ :
          Relational.LetSeq.Program T Γ ⟨k, bound, instrTrg op⟩) = _
      rw [ih]
      rfl
  | @let₁ k bound a b X Y dl dr ihp ihq =>
      exact congrArg₂ (fun (p : Relational.LetSeq.Program T Γ ⟨k, bound, X⟩)
        (q : Relational.LetSeq.Program T Γ ⟨k + 1, bound.snoc X, Y⟩) =>
        (⟨.let₁ p.1 q.1, .let₁ p.2 q.2⟩ : Relational.LetSeq.Program T Γ ⟨k, bound, Y⟩)) ihp ihq
  | @pair k bound a b X Y dl dr ihp ihq =>
      exact congrArg₂ (fun (p : Relational.LetSeq.Program T Γ ⟨k, bound, X⟩)
        (q : Relational.LetSeq.Program T Γ ⟨k, bound, Y⟩) =>
        (⟨.pair p.1 q.1, .pair p.2 q.2⟩ : Relational.LetSeq.Program T Γ ⟨k, bound, product X Y⟩)) ihp ihq
  | @let₂ k bound a b X Y Z dl dr ihp ihq =>
      exact congrArg₂ (fun (p : Relational.LetSeq.Program T Γ ⟨k, bound, product X Y⟩)
        (q : Relational.LetSeq.Program T Γ ⟨k + 2, (bound.snoc X).snoc Y, Z⟩) =>
        (⟨.let₂ p.1 q.1, .let₂ p.2 q.2⟩ : Relational.LetSeq.Program T Γ ⟨k, bound, Z⟩)) ihp ihq

omit [DecidableEq ν] [HasProduct τ] [HasUnit τ] in
private theorem seqTerm (f : S ⟶ T) {n : Nat} (t : LetSeq.LocallyNameless.Tm ν S.Instr n) :
    (LetPar.embed t).mapInstr f.instr = LetPar.embed (t.mapInstr f.instr) := by
  induction t <;> simp only [LetPar.embed, Parallel.Tm.mapInstr, LetSeq.LocallyNameless.Tm.mapInstr, *]

private theorem seq_cast {n : Nat} {β : BoundCtx τ n}
    {t : LetSeq.LocallyNameless.Tm ν T.Instr n} {A B : τ} (h : A = B)
    (d : LetSeq.LocallyNameless.Derivation T.Instr Γ β t A) :
    LetPar.derivation.{u, u, u} (h ▸ d : LetSeq.LocallyNameless.Derivation T.Instr Γ β t B) =
      Derivation.castResult h (LetPar.derivation.{u, u, u} d) := by
  cases h
  rfl

private theorem seqDerivation (f : S ⟶ T) {n : Nat} {β : BoundCtx τ n}
    {t : LetSeq.LocallyNameless.Tm ν S.Instr n} {A : τ}
    (d : LetSeq.LocallyNameless.Derivation S.Instr Γ β t A) :
    HEq ((LetPar.derivation.{u, u, u} d).mapInstr f) (LetPar.derivation.{u, u, u} (seqMap f d)) := by
  induction d with
  | @op k b p a d ih =>
      change HEq (Derivation.castResult.{u, u} (f.target p)
        (Derivation.op.{u, u, u} (tier := .seq) (f := f.instr p) (Derivation.castResult.{u, u} (f.source p).symm ((LetPar.derivation.{u, u, u} d).mapInstr f))))
        (LetPar.derivation.{u, u, u} (f.target p ▸
          LetSeq.LocallyNameless.Derivation.op (f := f.instr p) ((f.source p).symm ▸ seqMap f d)))
      rw [seq_cast]
      change HEq _ (Derivation.castResult.{u, u} (f.target p)
        (Derivation.op.{u, u, u} (tier := .seq) (f := f.instr p) (LetPar.derivation.{u, u, u} ((f.source p).symm ▸ seqMap f d))))
      rw [seq_cast]
      simp only [Derivation.castResult, eqRec_heq_iff, heq_eqRec_iff]
      congr 1
      · exact seqTerm f a
      · simpa only [eqRec_heq_iff, heq_eqRec_iff] using ih
  | _ =>
      simp only [LetPar.derivation, Derivation.mapInstr, seqMap]
      congr 1 <;> exact seqTerm f _

theorem ofLetSeq_map (f : S ⟶ T) (φ : Relational.LetSeq.Sentence S Γ) :
    (ofLetSeq φ).map f = ofLetSeq (Relational.LetSeq.Sentence.translate f φ) := by
  rw [Relational.LetSeq.Sentence.translate_endpoints]
  obtain ⟨⟨depth, bound, result⟩, ⟨l, dl⟩, ⟨r, dr⟩⟩ := φ
  simp only [ofLetSeq, Equation.ofLetSeq, Equation.map]
  erw [seqTranslate f dl, seqTranslate f dr]
  congr 1
  all_goals first | exact seqTerm f _ | exact seqDerivation f _

end Seq

section Case

variable [TypeFormers τ]

open Silmaril.Isotope.LetCase.LocallyNameless in
private def caseMap (g : S ⟶ T) : {n : Nat} → {β : BoundCtx τ n} → {t : Tm ν S.Instr n} →
    {A : τ} → Derivation S.Instr Γ β t A → Derivation T.Instr Γ β (t.mapInstr g.instr) A
  | _, _, _, _, .fv h => .fv h
  | _, _, _, _, .bv => .bv
  | _, _, _, _, .op (f := f) a =>
      g.target f ▸ .op (f := g.instr f) ((g.source f).symm ▸ caseMap g a)
  | _, _, _, _, .let₁ a b => .let₁ (caseMap g a) (caseMap g b)
  | _, _, _, _, .unit => .unit
  | _, _, _, _, .pair a b => .pair (caseMap g a) (caseMap g b)
  | _, _, _, _, .let₂ a b => .let₂ (caseMap g a) (caseMap g b)
  | _, _, _, _, .inl a => .inl (caseMap g a)
  | _, _, _, _, .inr b => .inr (caseMap g b)
  | _, _, _, _, .case e l r => .case (caseMap g e) (caseMap g l) (caseMap g r)
  | _, _, _, _, .abort a => .abort (caseMap g a)

private abbrev caseFold (f : S ⟶ T) {k : Nat} {bound : BoundCtx τ k}
    {a : Silmaril.Isotope.LetCase.LocallyNameless.Tm ν S.Instr k} {X : τ}
    (d : Silmaril.Isotope.LetCase.LocallyNameless.Derivation S.Instr Γ bound a X) :
    Relational.LetCase.Program T Γ ⟨k, bound, X⟩ :=
  Silmaril.Isotope.LetCase.LocallyNameless.Models.denote
    (Algebra.reductObj (Silmaril.Isotope.Institution.LetCase.sigHom Γ f)
      (Silmaril.Isotope.LetCase.LocallyNameless.Models.syntaxAlgebra T.Instr Γ)) d

private theorem caseTranslate (f : S ⟶ T) {k : Nat} {bound : BoundCtx τ k}
    {a : Silmaril.Isotope.LetCase.LocallyNameless.Tm ν S.Instr k} {X : τ}
    (d : Silmaril.Isotope.LetCase.LocallyNameless.Derivation S.Instr Γ bound a X) :
    Relational.LetCase.Program.translate f (i := ⟨k, bound, X⟩) ⟨a, d⟩ = ⟨a.mapInstr f.instr, caseMap f d⟩ := by
  refine (Relational.LetCase.Program.translate_eq_fold f
    (i := ⟨k, bound, X⟩) ⟨a, d⟩).trans ?_
  change caseFold f d = _
  induction d with
  | fv | bv | unit => rfl
  | @op k bound op a d ih =>
      refine (Relational.LetCase.Program.translate_eq_fold f
        (i := ⟨k, bound, instrTrg op⟩) ⟨.op op a, .op d⟩).symm.trans ?_
      refine (Relational.LetCase.Program.translate_op f op ⟨a, d⟩).trans ?_
      erw [Relational.LetCase.Program.translate_eq_fold f (i := ⟨k, bound, instrSrc op⟩) ⟨a, d⟩]
      change (⟨.op (f.instr op) (caseFold f d).1,
        f.target op ▸ .op ((f.source op).symm ▸ (caseFold f d).2)⟩ :
          Relational.LetCase.Program T Γ ⟨k, bound, instrTrg op⟩) = _
      rw [ih]
      rfl
  | @let₁ k bound a b X Y dl dr ihp ihq =>
      exact congrArg₂ (fun (p : Relational.LetCase.Program T Γ ⟨k, bound, X⟩)
        (q : Relational.LetCase.Program T Γ ⟨k + 1, bound.snoc X, Y⟩) =>
        (⟨.let₁ p.1 q.1, .let₁ p.2 q.2⟩ : Relational.LetCase.Program T Γ ⟨k, bound, Y⟩)) ihp ihq
  | @pair k bound a b X Y dl dr ihp ihq =>
      exact congrArg₂ (fun (p : Relational.LetCase.Program T Γ ⟨k, bound, X⟩)
        (q : Relational.LetCase.Program T Γ ⟨k, bound, Y⟩) =>
        (⟨.pair p.1 q.1, .pair p.2 q.2⟩ : Relational.LetCase.Program T Γ ⟨k, bound, product X Y⟩)) ihp ihq
  | @let₂ k bound a b X Y Z dl dr ihp ihq =>
      exact congrArg₂ (fun (p : Relational.LetCase.Program T Γ ⟨k, bound, product X Y⟩)
        (q : Relational.LetCase.Program T Γ ⟨k + 2, (bound.snoc X).snoc Y, Z⟩) =>
        (⟨.let₂ p.1 q.1, .let₂ p.2 q.2⟩ : Relational.LetCase.Program T Γ ⟨k, bound, Z⟩)) ihp ihq
  | @inl k bound a X Y d ihp =>
      exact congrArg (fun (p : Relational.LetCase.Program T Γ ⟨k, bound, X⟩) =>
        (⟨.inl p.1, .inl p.2⟩ : Relational.LetCase.Program T Γ ⟨k, bound, coprod X Y⟩)) ihp
  | @inr k bound a X Y d ihp =>
      exact congrArg (fun (p : Relational.LetCase.Program T Γ ⟨k, bound, Y⟩) =>
        (⟨.inr p.1, .inr p.2⟩ : Relational.LetCase.Program T Γ ⟨k, bound, coprod X Y⟩)) ihp
  | @case k bound e l r X Y Z de dl dr ihp ihq ihr =>
      exact congrArg₂ (fun (p : Relational.LetCase.Program T Γ ⟨k, bound, coprod X Y⟩)
        (branches : Relational.LetCase.Program T Γ ⟨k + 1, bound.snoc X, Z⟩ × Relational.LetCase.Program T Γ ⟨k + 1, bound.snoc Y, Z⟩) =>
        (⟨.case p.1 branches.1.1 branches.2.1, .case p.2 branches.1.2 branches.2.2⟩ :
          Relational.LetCase.Program T Γ ⟨k, bound, Z⟩)) ihp (congrArg₂ Prod.mk ihq ihr)
  | @abort k bound a X d ihp =>
      exact congrArg (fun (p : Relational.LetCase.Program T Γ ⟨k, bound, empty⟩) =>
        (⟨.abort p.1, .abort p.2⟩ : Relational.LetCase.Program T Γ ⟨k, bound, X⟩)) ihp

omit [DecidableEq ν] [TypeFormers τ] in
private theorem caseTerm (f : S ⟶ T) {n : Nat} (t : LetCase.LocallyNameless.Tm ν S.Instr n) :
    (LetParCase.embed t).mapInstr f.instr = LetParCase.embed (t.mapInstr f.instr) := by
  induction t <;>
    simp only [LetParCase.embed, Parallel.Tm.mapInstr, LetCase.LocallyNameless.Tm.mapInstr, *]

private theorem case_cast {n : Nat} {β : BoundCtx τ n}
    {t : LetCase.LocallyNameless.Tm ν T.Instr n} {A B : τ} (h : A = B)
    (d : LetCase.LocallyNameless.Derivation T.Instr Γ β t A) :
    LetParCase.derivation.{u, u, u} (h ▸ d : LetCase.LocallyNameless.Derivation T.Instr Γ β t B) =
      Derivation.castResult h (LetParCase.derivation.{u, u, u} d) := by
  cases h
  rfl

private theorem caseDerivation (f : S ⟶ T) {n : Nat} {β : BoundCtx τ n}
    {t : LetCase.LocallyNameless.Tm ν S.Instr n} {A : τ}
    (d : LetCase.LocallyNameless.Derivation S.Instr Γ β t A) :
    HEq ((LetParCase.derivation.{u, u, u} d).mapInstr f)
      (LetParCase.derivation.{u, u, u} (caseMap f d)) := by
  induction d with
  | @op k b p a d ih =>
      change HEq (Derivation.castResult.{u, u} (f.target p)
        (Derivation.op.{u, u, u} (tier := .case) (f := f.instr p) (Derivation.castResult.{u, u} (f.source p).symm ((LetParCase.derivation.{u, u, u} d).mapInstr f))))
        (LetParCase.derivation.{u, u, u} (f.target p ▸
          LetCase.LocallyNameless.Derivation.op (f := f.instr p) ((f.source p).symm ▸ caseMap f d)))
      rw [case_cast]
      change HEq _ (Derivation.castResult.{u, u} (f.target p)
        (Derivation.op.{u, u, u} (tier := .case) (f := f.instr p) (LetParCase.derivation.{u, u, u} ((f.source p).symm ▸ caseMap f d))))
      rw [case_cast]
      simp only [Derivation.castResult, eqRec_heq_iff, heq_eqRec_iff]
      congr 1
      · exact caseTerm f a
      · simpa only [eqRec_heq_iff, heq_eqRec_iff] using ih
  | _ =>
      simp only [LetParCase.derivation, Derivation.mapInstr, caseMap]
      congr 1 <;> exact caseTerm f _

theorem ofLetCase_map (f : S ⟶ T) (φ : Relational.LetCase.Sentence S Γ) :
    (ofLetCase φ).map f = ofLetCase (Relational.LetCase.Sentence.translate f φ) := by
  rw [Relational.LetCase.Sentence.translate_endpoints]
  obtain ⟨⟨depth, bound, result⟩, ⟨l, dl⟩, ⟨r, dr⟩⟩ := φ
  simp only [ofLetCase, Equation.ofLetCase, Equation.map]
  erw [caseTranslate f dl, caseTranslate f dr]
  congr 1
  all_goals first | exact caseTerm f _ | exact caseDerivation f _

end Case

theorem setM_eq_iff {A : Type v} (a b : SetM A) :
    a = b ↔ ∀ x, x ∈ a.run ↔ x ∈ b.run :=
  ⟨fun h => h ▸ fun _ => Iff.rfl, Set.ext⟩

end Silmaril.Isotope.Institution.Adapters.Powerset.Proofs

namespace Silmaril.Isotope.Institution.Adapters.Powerset.Proofs

open CategoryTheory Semantics Silmaril.Logic.Institution
open Parallel (Tier CaseTypes Control ParOp)
open Parallel.Institution

universe u v

variable {τ ε : Type u} {S T : InstrSig τ ε} {D : τ → Type v}
  {ν : Type u} [DecidableEq ν] {Γ : Ctx ν τ}

theorem toRelational_reduct (f : S ⟶ T) :
    Model.reductFunctor f ⋙ Model.toRelational (D := D) =
      Model.toRelational ⋙ Relational.Model.reductFunctor D f :=
  CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => Subsingleton.elim _ _)

section

variable [HasProduct τ] [HasUnit τ] [ProductModel D] [UnitModel D]

theorem room_sat_map {tier : Tier} [CaseTypes tier τ]
    (h : tier ≠ .iter) (C : Control tier D Id)
    (pair : ParOp (SetM : Type v → Type v)) (f : S ⟶ T)
    (X : Model D T) (φ : Equation S tier Γ) :
    (room h C Γ pair T).Sat X (φ.map f) ↔ (room h C Γ pair S).Sat (X.reduct f) φ := by
  change (φ.map f).Holds (X.toParallel pair) (lowerControl h C SetM) ↔
    φ.Holds ((X.reduct f).toParallel pair) (lowerControl h C SetM)
  refine (Equation.holds_map f φ (X.toParallel pair) _).trans ?_
  exact iff_of_eq (congrArg (fun Y => φ.Holds Y (lowerControl h C Y.M))
    (parallel_reduct f X pair).symm)

theorem ofLetSeq_sat (pair : ParOp (SetM : Type v → Type v)) (X : Model D S)
    (φ : Relational.LetSeq.Sentence S Γ) :
    (room (by decide) (Control.seq D Id) Γ pair S).Sat X (ofLetSeq φ) ↔
      Relational.LetSeq.Sentence.Satisfies X.relational φ := by
  change ((LetPar.observation Γ D).obj S).Sat (X.toParallel pair)
    (Equation.ofLetSeq φ.2.1.2 φ.2.2.2) ↔ _
  rw [Equation.ofLetSeq_sat]
  simp only [Relational.LetSeq.Sentence.Satisfies, LetSeq.LocallyNameless.Derivation.denoteRelation_iff_mem,
    Model.toParallel, setM_eq_iff]

end

section CaseSat

variable [TypeFormers τ] [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]

theorem ofLetCase_sat
    (pair : ParOp (SetM : Type v → Type v)) (X : Model D S)
    (φ : Relational.LetCase.Sentence S Γ) :
    (room (by decide) (Control.case D Id) Γ pair S).Sat X (ofLetCase φ) ↔
      Relational.LetCase.Sentence.Satisfies X.relational φ := by
  change ((LetParCase.observation Γ D).obj S).Sat (X.toParallel pair)
    (Equation.ofLetCase φ.2.1.2 φ.2.2.2) ↔ _
  rw [Equation.ofLetCase_sat]
  simp only [Relational.LetCase.Sentence.Satisfies, LetCase.LocallyNameless.Derivation.denoteRelation_iff_mem,
    Model.toParallel, setM_eq_iff]

end CaseSat
end Silmaril.Isotope.Institution.Adapters.Powerset.Proofs
