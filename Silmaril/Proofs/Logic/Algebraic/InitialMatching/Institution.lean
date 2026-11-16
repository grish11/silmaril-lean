module

public import Silmaril.Logic.Algebraic.Initial.Matching.Thms

set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Initial.Matching
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples

/-- Single-sort terms, interpreted in the actual public EQ algebras. -/
inductive Term (A : Signature) (k : Nat) where
  | var (i : Fin k)
  | app {n : Nat} (op : A.Op n) (args : Fin n → Term A k)

def Term.actual {A : Signature} {k : Nat} : Term A k → EQ.Term A.public (fun _ : Fin k => ()) ()
  | .var i => .var i
  | .app op args => .app op (fun i => (args i).actual)

def Term.map {A B : Signature} (f : A ⟶ B) {k : Nat} : Term A k → Term B k
  | .var i => .var i
  | .app op args => .app (f.operations op) (fun i => (args i).map f)

def Term.native {A : Signature} {k : Nat} : Term A k → Raw A k
  | .var i => .var i
  | .app op args => .app (.constructor op) (fun i => (args i).native)

@[simp] theorem Term.map_id {A : Signature} {k : Nat} (t : Term A k) : t.map (𝟙 A) = t := by
  induction t with
  | var => rfl
  | app op args ih => exact congrArg (Term.app op) (funext ih)
@[simp] theorem Term.map_comp {A B C : Signature} (f : A ⟶ B) (g : B ⟶ C) {k : Nat} (t : Term A k) :
    t.map (f ≫ g) = (t.map f).map g := by
  induction t with
  | var => rfl
  | app op args ih => exact congrArg (Term.app _) (funext ih)

theorem Term.actual_map {A B : Signature} (f : A ⟶ B) {k : Nat} (t : Term A k) :
    (t.map f).actual = t.actual.map (Signature.publicMap f) := by
  induction t with
  | var => rfl
  | app op args ih => exact congrArg (EQ.Term.app _) (funext ih)

theorem Term.native_map {A B : Signature} (f : A ⟶ B) {k : Nat} (t : Term A k) :
    (t.map f).native = t.native.map (nativeMap f) := by
  induction t with
  | var => rfl
  | app op args ih => exact congrArg (Silmaril.Logic.Matching.FirstOrder.Pattern.app _) (funext ih)

structure Equation (A : Signature) where
  count : Nat
  left : Term A count
  right : Term A count

def Equation.actual {A : Signature} (e : Equation A) : EQ.Equation A.public :=
  ⟨e.count, fun _ => (), (), e.left.actual, e.right.actual⟩
def Equation.map {A B : Signature} (f : A ⟶ B) (e : Equation A) : Equation B :=
  ⟨e.count, e.left.map f, e.right.map f⟩
def Equation.compile {A : Signature} (e : Equation A) : Silmaril.Logic.Matching.FixedPoint.Sentence (nativeSignature A) :=
  ⟨0, e.count, fun _ => (), fun _ => (), (), .base (equal e.left.native e.right.native)⟩

def Sentence (A : Signature) := Equation A ⊕ Constraint A
def Sentence.map {A B : Signature} (f : A ⟶ B) : Sentence A → Sentence B :=
  Sum.map (Equation.map f) (Constraint.map f)
def Sentence.Satisfies {A : Signature} (M : EQ.Algebra A.public) : Sentence A → Prop
  | .inl e => e.actual.Holds M
  | .inr p => Silmaril.Logic.Institution.Structured.Constraints.Sat Initial.equational M p.actual

def Sentence.compile {A : Signature} : Sentence A → Silmaril.Logic.Matching.FixedPoint.Sentence (nativeSignature A)
  | .inl e => e.compile
  | .inr p => Silmaril.Logic.Algebraic.Initial.Matching.compile p

@[simp] theorem Sentence.map_id {A : Signature} (p : Sentence A) : p.map (𝟙 A) = p := by
  rcases p with ⟨k, l, r⟩ | ⟨cs, ops⟩
  · change Sum.inl (Equation.map (𝟙 A) ⟨k, l, r⟩) = _
    simp only [Equation.map, Term.map_id]
  · rfl
@[simp] theorem Sentence.map_comp {A B C : Signature} (f : A ⟶ B) (g : B ⟶ C) (p : Sentence A) :
    p.map (f ≫ g) = (p.map f).map g := by
  rcases p with ⟨k, l, r⟩ | ⟨cs, ops⟩
  · change Sum.inl (Equation.map (f ≫ g) ⟨k, l, r⟩) = Sum.inl (Equation.map g (Equation.map f ⟨k, l, r⟩))
    simp only [Equation.map, Term.map_comp]
  · rfl

theorem nativeMap_id (A : Signature) : nativeMap (𝟙 A) = 𝟙 (nativeSignature A) := by
  apply ManySorted.Signature.Hom.ext
  intro n w s op
  cases op <;> rfl

theorem nativeMap_comp {A B C : Signature} (f : A ⟶ B) (g : B ⟶ C) :
    nativeMap (f ≫ g) = nativeMap f ≫ nativeMap g := by
  apply ManySorted.Signature.Hom.ext
  intro n w s op
  cases op <;> rfl

@[ext] theorem Model.ext {A : Signature} (M N : Model A) (h : M.native = N.native) : M = N := by
  cases M
  cases N
  cases h
  rfl

theorem Model.reduct_id {A : Signature} (M : Model A) : M.reduct (𝟙 A) = M := by
  apply Model.ext
  change Silmaril.Logic.Matching.FirstOrder.SignatureMap.reduct (nativeMap (𝟙 A)) M.native = M.native
  rw [nativeMap_id, Silmaril.Logic.Matching.FirstOrder.SignatureMap.reduct_id]

theorem Model.reduct_comp {A B C : Signature} (f : A ⟶ B) (g : B ⟶ C) (M : Model C) :
    M.reduct (f ≫ g) = (M.reduct g).reduct f := by
  apply Model.ext
  change Silmaril.Logic.Matching.FirstOrder.SignatureMap.reduct (nativeMap (f ≫ g)) M.native = _
  rw [nativeMap_comp]
  rfl

private theorem modelHom_hext {A : Signature} {M M' N N' : Model A} (hM : M = M') (hN : N = N')
    (f : M ⟶ N) (g : M' ⟶ N') (h : HEq f.map g.map) : HEq f g := by
  cases hM
  cases hN
  exact heq_of_eq (Silmaril.Logic.Matching.FirstOrder.Model.Hom.ext _ _ (eq_of_heq h))

theorem reductFunctor_id (A : Signature) : reductFunctor (𝟙 A) = 𝟭 (Model A) := by
  apply Functor.hext Model.reduct_id
  intro M N f
  exact modelHom_hext (M.reduct_id) (N.reduct_id) _ _ HEq.rfl

theorem reductFunctor_comp {A B C : Signature} (f : A ⟶ B) (g : B ⟶ C) :
    reductFunctor (f ≫ g) = reductFunctor g ⋙ reductFunctor f := by
  apply Functor.hext (Model.reduct_comp f g)
  intro M N h
  exact modelHom_hext (M.reduct_comp f g) (N.reduct_comp f g) _ _ HEq.rfl

/-- All native fixed-point sentences over independently structural models. -/
def target : Signature ⥤ Room where
  obj A := ⟨Silmaril.Logic.Matching.FixedPoint.Sentence (nativeSignature A), Cat.of (Model A),
    fun M p => p.Satisfies M.native⟩
  map f := ⟨fun p => p.map (nativeMap f), reductFunctor f, by
    intro M p
    exact ((Silmaril.Logic.Matching.FixedPoint.institution Unit).map (nativeMap f)).sat M.native p⟩
  map_id A := Room.hom_ext
    (funext fun p => by
      change p.map (nativeMap (𝟙 A)) = p
      rw [nativeMap_id]
      exact p.map_id) (reductFunctor_id A)
  map_comp f g := Room.hom_ext
    (funext fun p => by
      change p.map (nativeMap (f ≫ g)) = (p.map (nativeMap f)).map (nativeMap g)
      rw [nativeMap_comp]
      exact p.map_comp _ _) (reductFunctor_comp f g)

theorem Tree.eval_map {A B : Signature} (f : A ⟶ B) (p : Constraint A) (M : EQ.Algebra B.public) :
    Tree.eval (p.map f) M = Tree.eval p ((EQ.Algebra.reduct (Signature.publicMap f)).obj M) := by
  funext t
  induction t with
  | node c args ih => exact congrArg (M.op (f.operations (p.operation c))) (funext ih)

theorem Sentence.satisfaction {A B : Signature} (f : A ⟶ B) (M : EQ.Algebra B.public) (p : Sentence A) :
    (p.map f).Satisfies M ↔ p.Satisfies ((EQ.Algebra.reduct (Signature.publicMap f)).obj M) := by
  rcases p with e | p
  · change (∀ v, (e.left.map f).actual.eval M v = (e.right.map f).actual.eval M v) ↔ _
    simp only [Term.actual_map, EQ.Term.eval_map]
    rfl
  · change Silmaril.Logic.Institution.Structured.Constraints.Sat Initial.equational M (p.map f).actual ↔
      Silmaril.Logic.Institution.Structured.Constraints.Sat Initial.equational
        ((EQ.Algebra.reduct (Signature.publicMap f)).obj M) p.actual
    rw [actual_iff_fold_bijective, actual_iff_fold_bijective, Tree.eval_map]

def source : Signature ⥤ Room where
  obj A := ⟨Sentence A, Cat.of (EQ.Algebra A.public), Sentence.Satisfies⟩
  map f := ⟨Sentence.map f, EQ.Algebra.reduct (Signature.publicMap f), Sentence.satisfaction f⟩
  map_id _ := Room.hom_ext (funext Sentence.map_id) rfl
  map_comp f g := Room.hom_ext (funext (Sentence.map_comp f g)) rfl

theorem Term.denote_native {A : Signature} (M : Model A) {k : Nat} (t : Term A k)
    (v : Fin k → M.native.carrier ()) :
    M.native.denote v t.native = {t.actual.eval M.decode v} := by
  induction t with
  | var => rfl
  | app op args ih =>
    show M.native.denote v (Term.app op args).native = {(Term.app op args).actual.eval M.decode v}
    ext x
    change (∃ values, (∀ i, values i ∈ M.native.denote v (args i).native) ∧
      x ∈ M.native.operation (.constructor op) values) ↔ x = M.decode.op op (fun i => (args i).actual.eval M.decode v)
    constructor
    · show (∃ values, (∀ i, values i ∈ M.native.denote v (args i).native) ∧
        x ∈ M.native.operation (.constructor op) values) →
          x = M.decode.op op (fun i => (args i).actual.eval M.decode v)
      rintro ⟨values, hv, hx⟩
      have he : values = fun i => (args i).actual.eval M.decode v := by
        funext i
        have hh : values i ∈ ({(args i).actual.eval M.decode v} : Set (M.native.carrier ())) := by
          simpa only [ih i] using hv i
        exact hh
      have hvalue : x = M.decode.op op values := (M.constructor_mem_iff _ _ _).1 hx
      calc
        x = M.decode.op op values := hvalue
        _ = M.decode.op op (fun i => (args i).actual.eval M.decode v) := congrArg (M.decode.op op) he
    · intro hx
      refine ⟨_, ?_, (M.constructor_mem_iff _ _ _).2 hx⟩
      intro i
      rw [ih i]
      rfl

theorem Equation.compile_satisfies_iff {A : Signature} (M : Model A) (e : Equation A) :
    e.compile.Satisfies M.native ↔ e.actual.Holds M.decode := by
  change (∀ (v : Fin e.count → M.native.carrier ()) (η : Fin 0 → Set (M.native.carrier ())) x,
    x ∈ M.native.denote v (equal e.left.native e.right.native)) ↔ _
  constructor
  · intro h v
    exact (equal_mem M v _ _ _ _ (e.left.denote_native M v) (e.right.denote_native M v)
      (Classical.choice (M.native.nonempty ()))).1 (h v Fin.elim0 _)
  · intro h v η x
    exact (equal_mem M v _ _ _ _ (e.left.denote_native M v) (e.right.denote_native M v) x).2 (h v)

theorem Sentence.compile_satisfies_iff {A : Signature} (M : Model A) (p : Sentence A) :
    p.compile.Satisfies M.native ↔ p.Satisfies M.decode := by
  cases p with
  | inl e => exact e.compile_satisfies_iff M
  | inr p => exact compile_actual_iff p M

theorem map_disjunction {A B : Signature} (f : A ⟶ B) {r k : Nat} (ps : List (Pat A r k)) :
    (disjunction ps).map (nativeMap f) = disjunction (ps.map (fun p => p.map (nativeMap f))) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => exact congrArg₂ Silmaril.Logic.Matching.FixedPoint.Pattern.disj rfl ih

theorem map_conjunction {A B : Signature} (f : A ⟶ B) {r k : Nat} (ps : List (Pat A r k)) :
    (conjunction ps).map (nativeMap f) = conjunction (ps.map (fun p => p.map (nativeMap f))) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => exact congrArg₂ Silmaril.Logic.Matching.FixedPoint.Pattern.conj rfl ih

theorem map_closeAll {A B : Signature} (f : A ⟶ B) {r : Nat} : ∀ k (p : Pat A r k),
    (closeAll k p).map (nativeMap f) = closeAll k (p.map (nativeMap f)) := by
  intro k
  induction k with
  | zero => intro p; rfl
  | succ k ih => intro p; exact ih _

theorem map_disjointClause {A B : Signature} (f : A ⟶ B) (p : Constraint A)
    (c d : Fin p.constructors.count) :
    (disjointClause p c d).map (nativeMap f) = disjointClause (p.map f) c d := by
  by_cases h : c = d
  · simp only [disjointClause, h, ↓reduceIte]
    rfl
  · simp only [disjointClause, h, ↓reduceIte, map_closeAll]
    rfl

theorem map_injectiveClause {A B : Signature} (f : A ⟶ B) (p : Constraint A)
    (c : Fin p.constructors.count) (i : Fin (p.constructors.arity c)) :
    (injectiveClause p c i).map (nativeMap f) = injectiveClause (p.map f) c i := by
  rw [injectiveClause, map_closeAll]
  rfl

theorem map_noConfusion {A B : Signature} (f : A ⟶ B) (p : Constraint A) :
    (noConfusion p).map (nativeMap f) = noConfusion (p.map f) := by
  rw [noConfusion, map_conjunction]
  simp only [List.map_flatMap, List.map_append, List.map_map]
  apply congrArg conjunction
  apply congrArg (fun body => (List.finRange p.constructors.count).flatMap body)
  funext c
  apply congrArg₂ (· ++ ·)
  · apply congrArg (fun body => (List.finRange p.constructors.count).map body)
    funext d
    exact map_disjointClause f p c d
  · apply congrArg (fun body => (List.finRange (p.constructors.arity c)).map body)
    funext i
    exact map_injectiveClause f p c i

theorem map_generated {A B : Signature} (f : A ⟶ B) (p : Constraint A) :
    (generated p).map (nativeMap f) = generated (p.map f) := by
  apply congrArg Silmaril.Logic.Matching.FixedPoint.Pattern.mu
  exact (map_disjunction f ((List.finRange p.constructors.count).map fun c =>
    .app (.constructor (p.operation c)) (fun _ => .setvar 0))).trans (by
      simp only [List.map_map]
      rfl)

theorem Sentence.compile_map {A B : Signature} (f : A ⟶ B) (p : Sentence A) :
    (p.map f).compile = p.compile.map (nativeMap f) := by
  cases p with
  | inl e =>
    change Equation.compile (e.map f) = e.compile.map (nativeMap f)
    simp only [Equation.compile, Equation.map, Term.native_map]
    rfl
  | inr p =>
    change Silmaril.Logic.Algebraic.Initial.Matching.compile (p.map f) =
      (Silmaril.Logic.Algebraic.Initial.Matching.compile p).map (nativeMap f)
    apply congrArg (Silmaril.Logic.Matching.FixedPoint.Sentence.mk 0 0 (fun _ => ()) (fun _ => ()) ())
    exact congrArg₂ Silmaril.Logic.Matching.FixedPoint.Pattern.conj (map_generated f p).symm (map_noConfusion f p).symm

/-- The model square commutes on every actual algebra operation and every homomorphism. -/
theorem decode_reduct_square {A B : Signature} (f : A ⟶ B) :
    decodeFunctor B ⋙ EQ.Algebra.reduct (Signature.publicMap f) = reductFunctor f ⋙ decodeFunctor A := rfl

def translation : source ⟶ target where
  app A := ⟨Sentence.compile, decodeFunctor A, Sentence.compile_satisfies_iff⟩
  naturality := by
    intro A B f
    exact Room.hom_ext (funext (Sentence.compile_map f)) (decode_reduct_square f)

def toMatching : Inst.CoHom ⟨Signature, source⟩ ⟨Signature, target⟩ where
  Φ := 𝟭 _
  ρ := translation ≫ (Functor.leftUnitor target).inv

theorem toMatching_modelExpansive : toMatching.ModelExpansive := by
  intro A M
  exact ⟨expand M, decode_expand M⟩

theorem entails_iff (A : Signature) (H : Set (Sentence A)) (p : Sentence A) :
    (source.obj A).Entails H p ↔ (target.obj A).Entails (Sentence.compile '' H) p.compile :=
  toMatching.entails_iff toMatching_modelExpansive A H p

/-- Exact SAT transport quantifies over all actual source algebras and all structurally legal native models. -/
theorem satisfiable_iff (A : Signature) (H : Set (Sentence A)) :
    (∃ M : EQ.Algebra A.public, ∀ p ∈ H, p.Satisfies M) ↔
      ∃ N : Model A, ∀ q ∈ Sentence.compile '' H, q.Satisfies N.native := by
  constructor
  · rintro ⟨M, h⟩
    refine ⟨expand M, ?_⟩
    rintro q ⟨p, hp, rfl⟩
    apply (Sentence.compile_satisfies_iff _ _).2
    rw [decode_expand]
    exact h p hp
  · rintro ⟨N, h⟩
    exact ⟨N.decode, fun p hp => (Sentence.compile_satisfies_iff N p).1 (h _ ⟨p, hp, rfl⟩)⟩

theorem unsatisfiable_iff (A : Signature) (H : Set (Sentence A)) :
    (¬ ∃ M : EQ.Algebra A.public, ∀ p ∈ H, p.Satisfies M) ↔
      ¬ ∃ N : Model A, ∀ q ∈ Sentence.compile '' H, q.Satisfies N.native :=
  not_congr (satisfiable_iff A H)

end Silmaril.Logic.Algebraic.Initial.Matching
