module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Renaming.Defs

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open CategoryTheory Silmaril.Elgot.ITree
open Silmaril.Logic.ITree (Model)
open Isotope.Semantics (BoundEnv)
open LetCase.LocallyNameless (Derivation)
open LetCase.Structural.Finite (Context)
open LetCase.Structural.Reply (Γ₀)
open LetIter.PaperExpression.Source.FreeTree.Response (Structured.Event)
open Free
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

section Trees

variable {S T : Silmaril.Elgot.ITree.Signature.{0}} {X Y : Type 1}

/-- Request translation commutes with sequencing below a tree without
divergence. -/
theorem tree_bind_proof (f : S ⟶ T) {t : Tree S.Event X} (total : Total t) (k : X → Tree S.Event Y) :
    f.tree id (t >>= k) = (f.tree id t >>= fun x => f.tree id (k x)) := by
  induction total with
  | ret x =>
    rw [Silmaril.Elgot.ITree.Signature.Hom.tree_ret]
    exact (congrArg (f.tree id) (pure_bind x k)).trans (pure_bind x fun y => f.tree id (k y)).symm
  | vis e l _ ih =>
    rw [vis_bind, Silmaril.Elgot.ITree.Signature.Hom.tree_vis, Silmaril.Elgot.ITree.Signature.Hom.tree_vis, vis_bind]
    exact congrArg (vis _) (funext fun reply => ih _)

end Trees

variable {Φ Ψ : Type} [LetCase.Structural.Finite.Signature Ψ] (r : Φ → Ψ)

theorem tree_eval_proof (f : Pulled r) (x : Val (instrSrc f)) :
    (renameEvents r).tree id ((model (Pulled r)).eval f x) = (model Ψ).eval (Pulled.map r f) x := by
  have left := model_eval_bind f x (pure : _ → Tree (Events (Pulled r)) _)
  have right := model_eval_bind (Φ := Ψ) (Pulled.map r f) x (pure : _ → Tree (Events Ψ) _)
  rw [bind_pure] at left right
  rw [left, right, Silmaril.Elgot.ITree.Signature.Hom.tree_vis]
  exact congrArg (vis _) (funext fun reply => Silmaril.Elgot.ITree.Signature.Hom.tree_ret _ _ _)

set_option backward.isDefEq.respectTransparency false in
/-- The free tree of a renamed derivation is the request translation of
the free tree of the original derivation. -/
theorem tree_denote_proof {n : Nat} {γ : Context n} {t : LetCase.LocallyNameless.Tm Empty (Pulled r) n}
    {A : Ty Empty} (d : Derivation (Pulled r) Γ₀ γ t A) (ρ : BoundEnv Val γ) :
    (renameEvents r).tree id (d.denote Val (model (Pulled r)) (fun x => x.elim) ρ) =
      (renameDerivation r d).denote Val (model Ψ) (fun x => x.elim) ρ := by
  induction d with
  | fv h => rename_i x _; exact x.elim
  | bv => exact Silmaril.Elgot.ITree.Signature.Hom.tree_ret _ _ _
  | unit => exact Silmaril.Elgot.ITree.Signature.Hom.tree_ret _ _ _
  | op ha ih =>
    refine (tree_bind_proof _ (total_denote ha ρ) _).trans ?_
    rw [ih]
    exact bind_congr fun x => tree_eval_proof r _ x
  | let₁ ha hb iha ihb =>
    refine (tree_bind_proof _ (total_denote ha ρ) _).trans ?_
    rw [iha]
    exact bind_congr fun x => ihb _
  | pair ha hb iha ihb =>
    refine (tree_bind_proof _ (total_denote ha ρ) _).trans ?_
    rw [iha]
    refine bind_congr fun x => ?_
    refine (tree_bind_proof _ (total_denote hb ρ) _).trans ?_
    rw [ihb]
    exact bind_congr fun y => Silmaril.Elgot.ITree.Signature.Hom.tree_ret _ _ _
  | let₂ ha hc iha ihc =>
    refine (tree_bind_proof _ (total_denote ha ρ) _).trans ?_
    rw [iha]
    exact bind_congr fun x => ihc _
  | inl ha ih =>
    refine (tree_bind_proof _ (total_denote ha ρ) _).trans ?_
    rw [ih]
    exact bind_congr fun x => Silmaril.Elgot.ITree.Signature.Hom.tree_ret _ _ _
  | inr ha ih =>
    refine (tree_bind_proof _ (total_denote ha ρ) _).trans ?_
    rw [ih]
    exact bind_congr fun x => Silmaril.Elgot.ITree.Signature.Hom.tree_ret _ _ _
  | case he hl hr ihe ihl ihr =>
    refine (tree_bind_proof _ (total_denote he ρ) _).trans ?_
    rw [ihe]
    refine bind_congr fun x => ?_
    cases x with
    | inl a => exact ihl _
    | inr b => exact ihr _
  | abort ha ih =>
    refine (tree_bind_proof _ (total_denote ha ρ) _).trans ?_
    rw [ih]
    exact bind_congr fun x => nomatch x

private def requestKey : Request (Events Ψ) → (h : Ψ) × LetCase.Structural.Finite.Value (instrSrc h)
  | ⟨_, .call h argument⟩ => ⟨h, argument⟩

theorem renameRequest_injective_proof (injective : Function.Injective r) :
    Function.Injective (renameRequest r) := by
  rintro ⟨_, ⟨f, x⟩⟩ ⟨_, ⟨g, y⟩⟩ same
  have keys : (⟨Pulled.map r f, x⟩ : (h : Ψ) × LetCase.Structural.Finite.Value (instrSrc h)) =
      ⟨Pulled.map r g, y⟩ := congrArg requestKey same
  obtain ⟨instructions, arguments⟩ := Sigma.mk.inj keys
  obtain rfl : f = g := injective instructions
  cases eq_of_heq arguments
  rfl

theorem renameReply_bijective_proof (q : Request (Events (Pulled r))) :
    Function.Bijective ((renameEvents r).reply q) := by
  obtain ⟨_, ⟨f, x⟩⟩ := q
  exact Function.bijective_id

theorem reduct_allReplies_proof :
    (Logic.ITree.TraceInstitution.allRepliesModel (events Ψ)).reduct (renameEvents r) =
      Logic.ITree.TraceInstitution.allRepliesModel (events (Pulled r)) := by
  refine congrArg (Model.mk Unit fun _ => True) ?_
  funext q x reply y
  obtain ⟨_, ⟨f, argument⟩⟩ := q
  exact propext ⟨fun _ => trivial, fun _ => ⟨reply, rfl, trivial⟩⟩

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
