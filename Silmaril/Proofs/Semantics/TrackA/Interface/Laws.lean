module

public import Silmaril.Semantics.TrackA.Interface.Defs

public section

namespace Silmaril.Proofs.Semantics.TrackA.Interface

open Silmaril.Semantics.TrackA
open Interaction (Signature Node)

universe u v w x y z b c a s

variable {S : Signature.{u,v}} {T : Signature.{w,x}} {U : Signature.{y,z}}

namespace Signature

theorem hom_ext {f g : Signature.Hom S T}
    (requestEq : ∀ q, f.request q = g.request q)
    (responseEq : ∀ q (r : T.Response (f.request q)),
      f.response q r = g.response q (cast (congrArg T.Response (requestEq q)) r)) :
    f = g := by
  cases f with
  | mk fRequest fResponse =>
    cases g with
    | mk gRequest gResponse =>
      have h : fRequest = gRequest := funext requestEq
      subst gRequest
      have responses : fResponse = gResponse := funext fun q => funext fun r => by
        simpa using responseEq q r
      subst gResponse
      rfl

private theorem response_congr {f g : Signature.Hom S T} (h : f = g) (q : S.Request)
    (hq : f.request q = g.request q) (r : T.Response (f.request q)) :
    f.response q r = g.response q (cast (congrArg T.Response hq) r) := by
  cases h
  rfl

theorem inclusion_cancel {P : T.Request → Prop}
    {f g : Signature.Hom S (Interface.Signature.restrict T P)}
    (h : (Interface.Signature.inclusion P).comp f = (Interface.Signature.inclusion P).comp g) :
    f = g := by
  have requestEq (q : S.Request) : f.request q = g.request q :=
    Subtype.ext (congrArg (fun k : Signature.Hom S T => k.request q) h)
  apply hom_ext requestEq
  intro q r
  exact response_congr h q (congrArg Subtype.val (requestEq q)) r

theorem factors_iff (P : T.Request → Prop) (f : Signature.Hom S T) :
    (∃! g : Signature.Hom S (Interface.Signature.restrict T P),
      (Interface.Signature.inclusion P).comp g = f) ↔ ∀ q, P (f.request q) := by
  constructor
  · rintro ⟨g, hg, _⟩ q
    rw [← hg]
    exact (g.request q).property
  · intro lands
    refine ⟨Interface.Signature.factor P f lands, rfl, ?_⟩
    intro g hg
    exact inclusion_cancel hg

theorem copair_eta (h : Signature.Hom (Interface.Signature.sum S T) U) :
    Interface.Signature.copair (h.comp (Interface.Signature.inl S T))
      (h.comp (Interface.Signature.inr S T)) = h := by
  apply hom_ext (fun q => by cases q <;> rfl)
  intro q r
  cases q <;> rfl

end Signature

namespace Renaming

variable (f : Interface.Renaming S T)

private theorem response_cast {q q' : S.Request} (h : q = q') (r : S.Response q) :
    cast (congrArg T.Response (congrArg f.request h)) (f.response q r) =
      f.response q' (cast (congrArg S.Response h) r) := by
  subst q'
  rfl

theorem symm_comp_hom : f.symm.toHom.comp f.toHom = Signature.Hom.id S := by
  apply Signature.hom_ext (fun q => f.request.symm_apply_apply q)
  intro q r
  change (f.response q).symm
    (cast (congrArg T.Response (f.request.apply_symm_apply (f.request q)))
      (f.response (f.request.symm (f.request q)) r)) =
    cast (congrArg S.Response (f.request.symm_apply_apply q)) r
  exact (congrArg (f.response q).symm (response_cast f (f.request.symm_apply_apply q) r)).trans
    ((f.response q).symm_apply_apply _)

theorem comp_symm_hom : f.toHom.comp f.symm.toHom = Signature.Hom.id T := by
  apply Signature.hom_ext (fun q => f.request.apply_symm_apply q)
  intro q r
  change cast (congrArg T.Response (f.request.apply_symm_apply q))
    (f.response (f.request.symm q) ((f.response (f.request.symm q)).symm r)) =
    cast (congrArg T.Response (f.request.apply_symm_apply q)) r
  exact congrArg (cast (congrArg T.Response (f.request.apply_symm_apply q)))
    ((f.response (f.request.symm q)).apply_symm_apply r)

end Renaming

namespace Coalgebra

open Interface.Coalgebra

variable {B : Signature.{b,c}} {A : Type a} {X : Type s}
variable {c : Interaction.Coalgebra S B A X} {x : X} {a : A}

theorem hide_vis (P : S.Request → Prop) [DecidablePred P] (policy : Policy S P X)
    (refusal : A) {q : S.Request} {next : S.Response q → X}
    (layer : c x = .vis q next) (visible : P q) :
    hide P policy refusal c x = .vis ⟨q, visible⟩ next := by
  simp [hide, layer, visible]

theorem hide_reply (P : S.Request → Prop) [DecidablePred P] (policy : Policy S P X)
    (refusal : A) {q : S.Request} {next : S.Response q → X}
    (layer : c x = .vis q next) (hidden : ¬P q) {reply : S.Response q}
    (answers : policy x q hidden = some reply) :
    hide P policy refusal c x = .tau (next reply) := by
  simp [hide, layer, hidden, answers]

theorem hide_refuse (P : S.Request → Prop) [DecidablePred P] (policy : Policy S P X)
    (refusal : A) {q : S.Request} {next : S.Response q → X}
    (layer : c x = .vis q next) (hidden : ¬P q) (refuses : policy x q hidden = none) :
    hide P policy refusal c x = .ret refusal := by
  simp [hide, layer, hidden, refuses]

private theorem no_step_from_ret (layer : c x = .ret a) {label : Interaction.Coalgebra.Action S B}
    {y : X} (step : c.Step x label y) : False := by
  cases step with
  | tau edge => cases edge.symm.trans layer
  | choice edge _ => cases edge.symm.trans layer
  | vis edge _ => cases edge.symm.trans layer

private theorem no_internal_from_ret (layer : c x = .ret a) {y : X}
    (step : c.Internal x y) : False := by
  rcases step with step | ⟨_, _, _, step⟩
  · exact no_step_from_ret layer step
  · exact no_step_from_ret layer step

private theorem no_weak_step_from_ret (layer : c x = .ret a) {e : S.Exchange} {y : X}
    (step : c.WeakStep x e y) : False := by
  obtain ⟨mid, silent, exchange⟩ := step
  rcases silent.cases_head with rfl | ⟨_, first, _⟩
  · exact no_step_from_ret layer exchange
  · exact no_internal_from_ret layer first

theorem observes_ret (layer : c x = .ret a) :
    c.observes x = {Interaction.Trace.finite [] (.returned a)} := by
  ext trace
  constructor
  · intro run
    cases trace with
    | infinite events =>
      obtain ⟨path, start, steps⟩ := run
      exact (no_weak_step_from_ret layer (start ▸ steps 0)).elim
    | finite events ending =>
      obtain ⟨mid, last, follows, silent, ends⟩ := run
      cases follows with
      | cons first _ => exact (no_weak_step_from_ret layer first).elim
      | nil =>
        rcases silent.cases_head with rfl | ⟨_, first, _⟩
        · cases ending with
          | returned value =>
            have ret : c x = .ret value := ends
            obtain rfl := Node.ret.inj (ret.symm.trans layer)
            rfl
          | stuck q =>
            obtain ⟨_, _, edge⟩ := ends
            cases edge.symm.trans layer
          | deadlock kind =>
            obtain ⟨_, _, _, edge⟩ := ends
            cases edge.symm.trans layer
          | diverge =>
            obtain ⟨_, first, _⟩ := (show InfiniteTrace (c.Internal) x from ends).unfold
            exact (no_internal_from_ret layer first).elim
        · exact (no_internal_from_ret layer first).elim
  · intro member
    obtain rfl : trace = Interaction.Trace.finite [] (.returned a) := member
    exact ⟨x, x, .nil _, .refl, layer⟩

theorem hide_relabel_inclusion (P : S.Request → Prop) [DecidablePred P] (policy : Policy S P X)
    (refusal : A) (d : Interaction.Coalgebra (Interface.Signature.restrict S P) B A X) :
    hide P policy refusal (relabel (Interface.Signature.inclusion P) d) = d := by
  funext x
  cases layer : d x with
  | vis q next =>
    rcases q with ⟨q, visible⟩
    simp [hide, relabel, layer, Node.relabel, Interface.Signature.inclusion, visible]
  | ret a => simp [hide, relabel, layer, Node.relabel]
  | tau next => simp [hide, relabel, layer, Node.relabel]
  | branch kind shape next => simp [hide, relabel, layer, Node.relabel]

theorem hide_staged {P Q : S.Request → Prop} [decP : DecidablePred P] [DecidablePred Q]
    (subset : ∀ q, P q → Q q) (first : Policy S Q X)
    (second : Policy (Interface.Signature.restrict S Q) (fun q => P q.val) X)
    (refusal : A) (d : Interaction.Coalgebra S B A X) :
    relabel (Interface.Renaming.flatten subset).toHom
        (hide (fun q : (Interface.Signature.restrict S Q).Request => P q.val)
          (dec := fun q => decP q.val) second refusal
          (hide Q first refusal d)) =
      hide P (Policy.staged first second) refusal d := by
  funext x
  cases layer : d x with
  | ret a => simp [hide, relabel, layer, Node.relabel]
  | tau next => simp [hide, relabel, layer, Node.relabel]
  | branch kind shape next => simp [hide, relabel, layer, Node.relabel]
  | vis q next =>
    by_cases hq : Q q
    · by_cases hp : P q
      · simp [hide, relabel, layer, hq, hp, Node.relabel, Interface.Renaming.toHom,
          Interface.Renaming.flatten, Equiv.refl]
        rfl
      · cases reply : second x ⟨q, hq⟩ hp <;>
          simp [hide, relabel, layer, hq, hp, Policy.staged, reply, Node.relabel]
    · have hp : ¬P q := fun h => hq (subset q h)
      cases reply : first x q hq <;>
        simp [hide, relabel, layer, hq, hp, Policy.staged, reply, Node.relabel]

end Coalgebra
end Silmaril.Proofs.Semantics.TrackA.Interface
