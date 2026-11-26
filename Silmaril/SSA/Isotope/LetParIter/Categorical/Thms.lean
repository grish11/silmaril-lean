module

public import Silmaril.SSA.Isotope.LetParIter.Categorical.Laws.Defs
public import Silmaril.SSA.Isotope.LetParIter.Equations.Defs
public import Silmaril.SSA.Isotope.LetIter.Categorical.Soundness.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Substitution.Environment.Thms
import Silmaril.Proofs.SSA.Isotope.LetParIter.Categorical.Native
import Silmaril.Proofs.SSA.Isotope.LetParIter.Categorical.Renaming
import Silmaril.Proofs.SSA.Isotope.LetParIter.Categorical.Purity
import Silmaril.Proofs.SSA.Isotope.LetParIter.Categorical.Tuples
import Silmaril.Proofs.SSA.Isotope.LetParIter.Categorical.Assoc
import Silmaril.Proofs.SSA.Isotope.LetParIter.Categorical.Maps
import Silmaril.Proofs.SSA.Isotope.LetParIter.Categorical.GuardedCase
import Silmaril.Proofs.SSA.Isotope.LetParIter.Categorical.Iteration
import Silmaril.Proofs.SSA.Isotope.LetParIter.Categorical.Obstruction

/-! # Native agreement and soundness of the Par generators -/

public section

namespace Silmaril.Isotope.LetParIter.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Parallel (Derivation Pure)
open LetIter.Semantics.Categorical (TypeModel InstructionModel envObj envRenameMap)

universe v₁ v₂ u₁ u₂ u v w q

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] [∀ X Y : C, Preorder (X ⟶ Y)]
  (J : V ⥤ C) [StrongElgotFreydCategory J] (P : FreydCategory.OrderedParallel J)
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {ν : Type v} [DecidableEq ν] {Φ : Type w} [HasTy Φ τ] [InstructionModel J M Φ]
  {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}

/-- The existing exact native embedding preserves categorical denotation. -/
theorem denote_embed {t : LetIter.LocallyNameless.Tm ν Φ n} {A : τ}
    (d : LetIter.LocallyNameless.Derivation Φ Γ β t A) :
    denote J P M (derivation d) = LetIter.Semantics.Categorical.denote J M d :=
  denote_embed_proof J P M d

/-- Typed bound renaming applies the corresponding pure environment map. -/
theorem denote_rename {k : Nat} {δ : BoundCtx τ k} {t : Tm ν Φ n} {A : τ}
    (d : Derivation Φ Γ β t A) (r : BoundCtx.Renaming β δ) :
    denote J P M (Typing.rename r d) = J.map (envRenameMap M Γ r) ≫ denote J P M d :=
  denote_rename_proof J P M d r

/-- Swapping the returned tuple exchanges the parallel branches. -/
theorem swap_sound {a b : Tm ν Φ n} {A B : τ}
    (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b B) :
    denote J P M (Typing.swap (.par da db)) = denote J P M (.par db da) :=
  swap_sound_proof J P M da db

/-- The typed reassociation term transports three parallel result positions. -/
theorem assoc_sound {a b c : Tm ν Φ n} {A B D : τ}
    (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b B) (dc : Derivation Φ Γ β c D) :
    denote J P M (Typing.assoc (.par (.par da db) dc)) =
      denote J P M (.par da (.par db dc)) :=
  assoc_sound_proof J P M da db dc

/-- Projecting away a pure left unit leaves the right branch. -/
theorem unitLeft_sound {a : Tm ν Φ n} {A : τ} (d : Derivation Φ Γ β a A) :
    denote J P M (Typing.dropLeft (.par .unit d)) = denote J P M d :=
  unitLeft_sound_proof J P M d

/-- Projecting away a pure right unit leaves the left branch. -/
theorem unitRight_sound {a : Tm ν Φ n} {A : τ} (d : Derivation Φ Γ β a A) :
    denote J P M (Typing.dropRight (.par d .unit)) = denote J P M d :=
  unitRight_sound_proof J P M d

/-- Retaining the context and returning just the newest slot preserves the denotation. -/
theorem letEta_sound {a : Tm ν Φ n} {A : τ} (d : Derivation Φ Γ β a A) :
    denote J P M (.let₁ d Typing.newest) = denote J P M d :=
  letEta_sound_proof J P M d

/-- A mixed loop can first bind its initial state and then start at the bound value. -/
theorem iterBind_sound {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ (.snoc β A) b (coprod B A)) :
    denote J P M (.iter (h := rfl) da db) =
      denote J P M (.let₁ da (.iter (h := rfl) Typing.newest (Typing.underBinder db))) :=
  iterBind_sound_proof J P M da db

/-- A mixed loop unfolds one step and recurs only on the feedback branch. -/
theorem iterFixpoint_sound {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ (.snoc β A) b (coprod B A)) :
    denote J P M (.iter (h := rfl) da db) =
      denote J P M (.let₁ da (.case (h := hasCase) db Typing.newest
        (.iter (h := rfl) Typing.newest (Typing.underBinder (Typing.underBinder db))))) :=
  iterFixpoint_sound_proof J P M da db

variable {ε : Type q} [HasEff Φ ε] {pe : ε}
  (pureInstr : ∀ f : Φ, IsPure pe f →
    ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
      InstructionModel.denote (J := J) (M := M) f = J.map p)

include pureInstr

/-- Transfer an exact LetIter equivalence under the native categorical soundness
hypotheses. The proof-relevant relation in `Equiv.native` carries its own witnesses. -/
theorem embed_equiv_of_coherent_shared_tensor [FreydCategory.CentralUnit J]
    (coherent : LetIter.Semantics.Categorical.TypingCoherent (ν := ν) J M Φ)
    (shared : ∀ R S : V, ∃ e : J.obj R ⊗ J.obj S = J.obj (R ⊗ S),
      Functor.StrongPremonoidal.tensorIso (J := J) R S = eqToIso e)
    {a b : LetIter.LocallyNameless.Tm ν Φ n} {A : τ}
    (da : LetIter.LocallyNameless.Derivation Φ Γ β a A)
    (db : LetIter.LocallyNameless.Derivation Φ Γ β b A)
    (h : LetIter.LocallyNameless.Equiv pe Γ β a b A) :
    denote J P M (derivation da) = denote J P M (derivation db) := by
  simpa only [denote_embed] using
    LetIter.Semantics.Categorical.denote_equiv_of_coherent_shared_tensor J M
      coherent shared pureInstr h da db

/-- The syntactic purity judgment factors the mixed denotation through the value functor. -/
theorem denote_pure {t : Tm ν Φ n} {A : τ} (d : Derivation Φ Γ β t A) (h : Pure pe t) :
    ∃ p : envObj M Γ β ⟶ M.obj A, denote J P M d = J.map p :=
  denote_pure_proof J P M pureInstr d h

/-- Parallel and sequential pairing agree on two pure terms. -/
theorem purePair_sound {a b : Tm ν Φ n} {A B : τ}
    (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b B) (ha : Pure pe a) (hb : Pure pe b) :
    denote J P M (.par da db) = denote J P M (.pair da db) :=
  purePair_sound_proof J P M pureInstr da db ha hb

variable (L : Laws J P)

include L

/-- Each pure continuation can read the retained context and its own branch result. -/
theorem map_sound {a b : Tm ν Φ n} {f g : Tm ν Φ (n + 1)} {A B D E : τ}
    (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b B)
    (df : Derivation Φ Γ (.snoc β A) f D) (dg : Derivation Φ Γ (.snoc β B) g E)
    (hf : Pure pe f) (hg : Pure pe g) :
    denote J P M (.par (.let₁ da df) (.let₁ db dg)) =
      denote J P M (.let₂ (.par da db) (.pair (Typing.leftResult df) (Typing.underBinder dg))) :=
  map_sound_proof J P M L pureInstr da db df dg hf hg

/-- A pure scrutinee in the left branch can select its arm before the fork. -/
theorem parCaseLeft_sound {e p : Tm ν Φ n} {l r : Tm ν Φ (n + 1)} {A B D E : τ}
    (de : Derivation Φ Γ β e (coprod A B)) (he : Pure pe e)
    (dl : Derivation Φ Γ (.snoc β A) l D) (dr : Derivation Φ Γ (.snoc β B) r D)
    (dp : Derivation Φ Γ β p E) :
    denote J P M (.par (.case (h := hasCase) de dl dr) dp) =
      denote J P M
        (.case (h := hasCase) de (.par dl (Typing.lift dp)) (.par dr (Typing.lift dp))) :=
  parCaseLeft_sound_proof J P M L pureInstr de he dl dr dp

/-- A pure scrutinee in the right branch can select its arm before the fork. -/
theorem parCaseRight_sound {e p : Tm ν Φ n} {l r : Tm ν Φ (n + 1)} {A B D E : τ}
    (de : Derivation Φ Γ β e (coprod A B)) (he : Pure pe e)
    (dl : Derivation Φ Γ (.snoc β A) l D) (dr : Derivation Φ Γ (.snoc β B) r D)
    (dp : Derivation Φ Γ β p E) :
    denote J P M (.par dp (.case (h := hasCase) de dl dr)) =
      denote J P M
        (.case (h := hasCase) de (.par (Typing.lift dp) dl) (.par (Typing.lift dp) dr)) :=
  parCaseRight_sound_proof J P M L pureInstr de he dl dr dp

omit L pureInstr in
/-- The native let eta countermodel obstructs universal existence of ordered parallel. -/
theorem not_all_models_extend :
    ¬ (∀ {V C : Type 1} [Category.{0} V] [Category.{0} C]
      [CartesianMonoidalCategory V] [SymmetricCategory V]
      [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
      [HasFiniteCoproducts V] [HasFiniteCoproducts C]
      [DistributiveTensor V] [DistributivePremonoidalCategory C]
      [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J],
      ∃ order : ∀ X Y : C, Preorder (X ⟶ Y),
        letI := order
        Nonempty (FreydCategory.OrderedParallel J)) :=
  not_all_models_extend_proof

end Silmaril.Isotope.LetParIter.Categorical
