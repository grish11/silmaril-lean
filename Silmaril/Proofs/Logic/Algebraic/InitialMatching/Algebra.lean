module

public import Silmaril.Logic.Algebraic.Initial.Matching.Defs

set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Initial.Matching
open CategoryTheory CategoryTheory.Limits Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples

/-- The constructor domain itself, without identifying any distinct symbols. -/
def identityConstraint (A : Constructors) : Constraint A.signature :=
  ⟨A, fun c => ⟨c, rfl⟩⟩

def treeAlgebra (A : Constructors) : EQ.Algebra A.signature.public where
  carrier _ := Tree A
  op := fun ⟨c, h⟩ args => .node c (fun i => args (Fin.cast h i))

abbrev fold (A : Constructors) (M : EQ.Algebra A.signature.public) := Tree.eval (identityConstraint A) M

def foldHom (A : Constructors) (M : EQ.Algebra A.signature.public) : treeAlgebra A ⟶ M where
  map s := by cases s; exact fold A M
  map_op := by
    intro n w s op args
    have hw : w = fun _ => () := by funext i; cases w i; rfl
    subst w
    cases s
    rcases op with ⟨c, h⟩
    cases h
    rfl

/-- Actual homomorphisms out of the constructor trees are forced by recursion. -/
theorem fold_unique (A : Constructors) (M : EQ.Algebra A.signature.public)
    (f : treeAlgebra A ⟶ M) : foldHom A M = f := by
  apply Initial.algebraHom_ext
  funext s t
  cases s
  induction t with
  | node c args ih =>
    change M.op ⟨c, rfl⟩ (fun i => fold A M (args i)) = f.map () (.node c args)
    rw [show f.map () (.node c args) = M.op ⟨c, rfl⟩ (fun i => f.map () (args i)) from
      f.map_op (w := fun _ => ()) (s := ()) ⟨c, rfl⟩ args]
    exact congrArg (M.op ⟨c, rfl⟩) (funext ih)

def tree_isInitial (A : Constructors) : IsInitial (treeAlgebra A) :=
  IsInitial.ofUniqueHom (foldHom A) (fun M f => (fold_unique A M f).symm)

/-- An actual bijective algebra homomorphism has an inverse algebra homomorphism. -/
def algebraIsoOfBijective {A : EQ.Signature} {M N : EQ.Algebra A} (f : M ⟶ N)
    (hf : ∀ s, Function.Bijective (f.map s)) : M ≅ N := by
  let e (s) := Equiv.ofBijective (f.map s) (hf s)
  let g : N ⟶ M :=
    { map := fun s => (e s).symm
      map_op := by
        intro n w s op args
        apply (hf s).1
        change (e s) ((e s).symm (N.op op args)) = f.map s (M.op op (fun i => (e (w i)).symm (args i)))
        rw [Equiv.apply_symm_apply, f.map_op]
        exact congrArg (N.op op) (funext fun i => ((e (w i)).apply_symm_apply (args i)).symm) }
  exact
    { hom := f
      inv := g
      hom_inv_id := by
        apply Initial.algebraHom_ext
        funext s x
        exact (e s).symm_apply_apply x
      inv_hom_id := by
        apply Initial.algebraHom_ext
        funext s x
        exact (e s).apply_symm_apply x }

/-- The canonical fold is bijective exactly for actual initial algebras. -/
theorem initial_iff_fold_bijective (A : Constructors) (M : EQ.Algebra A.signature.public) :
    Nonempty (IsInitial M) ↔ Function.Bijective (fold A M) := by
  constructor
  · rintro ⟨hM⟩
    let f := foldHom A M
    let g := hM.to (treeAlgebra A)
    have left : f ≫ g = 𝟙 (treeAlgebra A) := (tree_isInitial A).hom_ext _ _
    have right : g ≫ f = 𝟙 M := hM.hom_ext _ _
    constructor
    · intro x y h
      have hx : g.map () (f.map () x) = x := congrArg (fun q => q.map () x) left
      have hy : g.map () (f.map () y) = y := congrArg (fun q => q.map () y) left
      exact hx.symm.trans ((congrArg (g.map ()) h).trans hy)
    · intro x
      exact ⟨g.map () x, congrArg (fun q => q.map () x) right⟩
  · intro h
    have hh : ∀ s, Function.Bijective ((foldHom A M).map s) := by
      intro s; cases s; exact h
    exact ⟨(tree_isInitial A).ofIso (algebraIsoOfBijective (foldHom A M) hh)⟩

/-- There is no extra initiality hypothesis hidden in the empty-theory wrapper. -/
theorem emptyModel_initial_iff {A : EQ.Signature} (M : EQ.Algebra A) :
    Nonempty (IsInitial (Silmaril.Logic.Institution.Structured.SemanticModels.emptyModel
      Initial.equational A M)) ↔ Nonempty (IsInitial M) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨IsInitial.ofUniqueHom
      (fun N => (h.to (Silmaril.Logic.Institution.Structured.SemanticModels.emptyModel
        Initial.equational A N)).hom)
      (by
        intro N f
        exact congrArg (fun q => q.hom) (h.hom_ext
          (⟨f⟩ : (Silmaril.Logic.Institution.Structured.SemanticModels.emptyModel Initial.equational A M) ⟶
            Silmaril.Logic.Institution.Structured.SemanticModels.emptyModel Initial.equational A N)
          (h.to _)))⟩
  · rintro ⟨h⟩
    exact ⟨IsInitial.ofUniqueHom (fun N => ⟨h.to N.obj⟩) (by
      intro N f
      apply ObjectProperty.hom_ext
      exact h.hom_ext _ _)⟩

/-- The selected sentence is precisely the existing actual freeness constraint. -/
theorem actual_iff_fold_bijective {B : Signature} (p : Constraint B) (M : EQ.Algebra B.public) :
    Silmaril.Logic.Institution.Structured.Constraints.Sat Initial.equational M p.actual ↔
      Function.Bijective (Tree.eval p M) := by
  rw [Constraint.actual, Silmaril.Logic.Institution.Structured.Constraints.satisfaction]
  let R := (EQ.Algebra.reduct (Signature.publicMap p.context)).obj M
  have he : fold p.constructors R = Tree.eval p M := by
    funext t
    induction t with
    | node c args ih =>
      change M.op (p.operation c) (fun i => fold p.constructors R (args i)) =
        M.op (p.operation c) (fun i => Tree.eval p M (args i))
      exact congrArg (M.op (p.operation c)) (funext ih)
  exact (Initial.initialConstraint_sat_iff _
    (Silmaril.Logic.Institution.Structured.SemanticModels.emptyModel Initial.equational _ R)).trans
      ((emptyModel_initial_iff R).trans (by simpa only [he] using initial_iff_fold_bijective p.constructors R))

/-- No confusion implies injectivity of the independent tree fold. -/
theorem fold_injective_of_noConfusion {B : Signature} (p : Constraint B) (M : EQ.Algebra B.public)
    (hn : NoConfusion p M) : Function.Injective (Tree.eval p M) := by
  intro t
  induction t with
  | node c args ih =>
    intro u h
    cases u with
    | node d other =>
      by_cases he : c = d
      · subst d
        have ha := hn.1 c h
        exact congrArg (Tree.node c) (funext fun i => ih i (congrFun ha i))
      · exact (hn.2 c d he _ _ h).elim

/-- Bijectivity detects both junk and collapsed constructors. -/
theorem noConfusion_of_fold_bijective {B : Signature} (p : Constraint B) (M : EQ.Algebra B.public)
    (h : Function.Bijective (Tree.eval p M)) : NoConfusion p M := by
  let pre (x : M.carrier ()) : Tree p.constructors := Classical.choose (h.2 x)
  have hp (x : M.carrier ()) : Tree.eval p M (pre x) = x := Classical.choose_spec (h.2 x)
  constructor
  · intro c xs ys he
    have ht : Tree.node c (fun i => pre (xs i)) = Tree.node c (fun i => pre (ys i)) := by
      apply h.1
      simpa only [Tree.eval, hp] using he
    have hs : (fun i => pre (xs i)) = fun i => pre (ys i) := by
      exact eq_of_heq (Tree.node.inj ht).2
    funext i
    exact (hp (xs i)).symm.trans ((congrArg (Tree.eval p M) (congrFun hs i)).trans (hp (ys i)))
  · intro c d hcd xs ys he
    have ht : Tree.node c (fun i => pre (xs i)) = Tree.node d (fun i => pre (ys i)) := by
      apply h.1
      simpa only [Tree.eval, hp] using he
    have hc : c = d := congrArg (fun t => match t with | .node c _ => c) ht
    exact hcd hc

theorem bijective_iff_generated_noConfusion {B : Signature} (p : Constraint B) (M : EQ.Algebra B.public) :
    Function.Bijective (Tree.eval p M) ↔ Generated p M ∧ NoConfusion p M :=
  ⟨fun h => ⟨h.2, noConfusion_of_fold_bijective p M h⟩,
    fun h => ⟨fold_injective_of_noConfusion p M h.2, h.1⟩⟩

end Silmaril.Logic.Algebraic.Initial.Matching
