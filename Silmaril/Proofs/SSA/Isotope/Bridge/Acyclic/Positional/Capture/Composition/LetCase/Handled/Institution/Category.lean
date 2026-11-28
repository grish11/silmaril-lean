module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Renaming.Category.Defs

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open CategoryTheory Silmaril.Elgot.ITree
open Silmaril.Logic.ITree (Model)
open Silmaril.Isotope.Institution (InstrSig)
open Silmaril.Isotope.Institution.Acyclic (CaseEquation)
open LetCase.Structural.Finite (Shape)
open LetCase.Structural.Reply (Γ₀)
open Free (Events)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

theorem shape_ty_injective_proof : Function.Injective Shape.ty := by
  intro a
  induction a with
  | unit =>
    intro b same
    cases b <;> first | rfl | cases same
  | pair l r ihl ihr =>
    intro b same
    cases b with
    | pair l' r' =>
      obtain ⟨left, right⟩ := Ty.product.inj same
      rw [ihl left, ihr right]
    | unit => cases same
    | sum _ _ => cases same
  | sum l r ihl ihr =>
    intro b same
    cases b with
    | sum l' r' =>
      obtain ⟨left, right⟩ := Ty.coprod.inj same
      rw [ihl left, ihr right]
    | unit => cases same
    | pair _ _ => cases same

/-- Every relabelling into a structural signature is a pulled-back
renaming: its source signature is the target read through the map. -/
theorem hom_cases_proof {Ψ : Type} [LetCase.Structural.Finite.Signature Ψ]
    (motive : ∀ {Φ : Type} [LetCase.Structural.Finite.Signature Φ], (sig Φ ⟶ sig Ψ) → Prop)
    (pulled : ∀ {Φ : Type} (r : Φ → Ψ), motive (pulledHom r))
    {Φ : Type} [inst : LetCase.Structural.Finite.Signature Φ] (f : sig Φ ⟶ sig Ψ) : motive f := by
  rcases f with ⟨r, source, target, effect⟩
  change Φ → Ψ at r
  have same : inst = inferInstanceAs (LetCase.Structural.Finite.Signature (Pulled r)) := by
    cases inst with
    | mk src trg =>
      exact congrArg₂ LetCase.Structural.Finite.Signature.mk
        (funext fun x => (shape_ty_injective_proof (source x)).symm)
        (funext fun x => (shape_ty_injective_proof (target x)).symm)
  subst same
  exact pulled r

variable {Φ Ψ Ω : Type} [LetCase.Structural.Finite.Signature Φ] [LetCase.Structural.Finite.Signature Ψ]
  [LetCase.Structural.Finite.Signature Ω]

theorem eventsHom_pulled_proof {Φ : Type} (r : Φ → Ψ) : eventsHom (pulledHom r) = renameEvents r :=
  Silmaril.Elgot.ITree.Signature.Hom.ext _ _ fun q => by
    obtain ⟨_, ⟨x, argument⟩⟩ := q
    rfl

theorem eventsHom_id_proof : eventsHom (𝟙 (sig Φ)) = 𝟙 (events Φ).toSignature :=
  Silmaril.Elgot.ITree.Signature.Hom.ext _ _ fun q => by
    obtain ⟨_, ⟨x, argument⟩⟩ := q
    rfl

private theorem eventsHom_comp_pulled {Ψ₀ : Type} (s : Ψ₀ → Ω) :
    ∀ {Φ : Type} [LetCase.Structural.Finite.Signature Φ] (f : sig Φ ⟶ sig (Pulled s)),
      eventsHom (f ≫ pulledHom s) = eventsHom f ≫ eventsHom (pulledHom s) := by
  intro Φ inst f
  exact hom_cases_proof (Ψ := Pulled s)
    (fun {Φ} [LetCase.Structural.Finite.Signature Φ] f =>
      eventsHom (f ≫ pulledHom s) = eventsHom f ≫ eventsHom (pulledHom s))
    (fun r => Silmaril.Elgot.ITree.Signature.Hom.ext _ _ fun q => by
      obtain ⟨_, ⟨x, argument⟩⟩ := q
      rfl) f

theorem eventsHom_comp_proof (g : sig Ψ ⟶ sig Ω) :
    ∀ {Φ : Type} [LetCase.Structural.Finite.Signature Φ] (f : sig Φ ⟶ sig Ψ),
      eventsHom (f ≫ g) = eventsHom f ≫ eventsHom g :=
  hom_cases_proof (Ψ := Ω)
    (fun {Ψ} [LetCase.Structural.Finite.Signature Ψ] g => ∀ {Φ : Type}
      [LetCase.Structural.Finite.Signature Φ] (f : sig Φ ⟶ sig Ψ),
      eventsHom (f ≫ g) = eventsHom f ≫ eventsHom g)
    (fun s => eventsHom_comp_pulled s) g

theorem eventsRequest_injective_proof (f : sig Φ ⟶ sig Ψ) :
    Function.Injective f.instr → Function.Injective (eventsRequest f) :=
  hom_cases_proof (Ψ := Ψ)
    (fun {Φ} [LetCase.Structural.Finite.Signature Φ] f =>
      Function.Injective f.instr → Function.Injective (eventsRequest f))
    (fun r injective => by
      have same : eventsRequest (pulledHom r) = renameRequest r :=
        funext fun q => by obtain ⟨_, ⟨x, argument⟩⟩ := q; rfl
      rw [same]
      exact renameRequest_injective r injective) f

theorem eventsReply_bijective_proof (f : sig Φ ⟶ sig Ψ) (q : Request (Events Φ)) :
    Function.Bijective ((eventsHom f).reply q) := by
  obtain ⟨_, ⟨x, argument⟩⟩ := q
  exact cast_bijective _

theorem satLe_hom_proof (f : sig Φ ⟶ sig Ψ) : Function.Injective f.instr → ∀ (N : HandledModel Ψ)
    (e : CaseEquation (sig Φ)),
    SatLe N (((Silmaril.Isotope.Institution.LetCase.inst (ε := Bool) Γ₀).map f).sen e) ↔
      SatLe (N.reduct (eventsHom f)) e :=
  hom_cases_proof (Ψ := Ψ)
    (fun {Φ} [LetCase.Structural.Finite.Signature Φ] f => Function.Injective f.instr →
      ∀ (N : HandledModel Ψ) (e : CaseEquation (sig Φ)),
        SatLe N (((Silmaril.Isotope.Institution.LetCase.inst (ε := Bool) Γ₀).map f).sen e) ↔
          SatLe (N.reduct (eventsHom f)) e)
    (fun r injective N e => by
      rw [renameCase_eq_inst, eventsHom_pulled_proof]
      exact satLe_rename injective N e) f

theorem reduct_allReplies_hom_proof (f : sig Φ ⟶ sig Ψ) :
    (Logic.ITree.TraceInstitution.allRepliesModel (events Ψ)).reduct (eventsHom f) =
      Logic.ITree.TraceInstitution.allRepliesModel (events Φ) :=
  hom_cases_proof (Ψ := Ψ)
    (fun {Φ} [LetCase.Structural.Finite.Signature Φ] f =>
      (Logic.ITree.TraceInstitution.allRepliesModel (events Ψ)).reduct (eventsHom f) =
        Logic.ITree.TraceInstitution.allRepliesModel (events Φ))
    (fun r => by rw [eventsHom_pulled_proof]; exact reduct_allReplies r) f

theorem traceHom_ext_proof {S T : TraceSignature.{0}} {f g : S ⟶ T} (same : f.hom = g.hom) : f = g := by
  obtain ⟨_, _, _⟩ := f
  obtain ⟨_, _, _⟩ := g
  cases same
  rfl

theorem reductFunctor_id_proof : reductFunctor (𝟙 (sig Φ)) = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun N => ?_)
  obtain ⟨M⟩ := N
  refine congrArg Discrete.mk ?_
  change M.reduct (eventsHom (𝟙 (sig Φ))) = M
  rw [eventsHom_id_proof]
  exact Model.reduct_id M

theorem reductFunctor_comp_proof (f : sig Φ ⟶ sig Ψ) (g : sig Ψ ⟶ sig Ω) :
    reductFunctor (f ≫ g) = reductFunctor g ⋙ reductFunctor f := by
  refine CategoryTheory.Functor.ext (fun N => ?_)
  obtain ⟨M⟩ := N
  refine congrArg Discrete.mk ?_
  change M.reduct (eventsHom (f ≫ g)) = (M.reduct (eventsHom g)).reduct (eventsHom f)
  rw [eventsHom_comp_proof g f]
  exact Model.reduct_comp _ _ M

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
