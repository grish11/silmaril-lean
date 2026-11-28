module

public import Silmaril.Semantics.TrackA.Interface.Defs
public import Silmaril.Semantics.TrackA.Interaction.Thms
import Silmaril.Proofs.Semantics.TrackA.Interface.Laws

public section

namespace Silmaril.Semantics.TrackA.Interface

open Interaction (Node)

universe u v w x y z b c a s

variable {S : Interaction.Signature.{u,v}} {T : Interaction.Signature.{w,x}}
variable {U : Interaction.Signature.{y,z}}

namespace Signature

/-- Equality of request maps and of response decoders after fiber transport. -/
theorem hom_ext {f g : Interaction.Signature.Hom S T}
    (requestEq : ∀ q, f.request q = g.request q)
    (responseEq : ∀ q (r : T.Response (f.request q)),
      f.response q r = g.response q (cast (congrArg T.Response (requestEq q)) r)) :
    f = g :=
  Proofs.Semantics.TrackA.Interface.Signature.hom_ext requestEq responseEq

@[simp] theorem inclusion_factor (P : T.Request → Prop) (f : Interaction.Signature.Hom S T)
    (lands : ∀ q, P (f.request q)) : (inclusion P).comp (factor P f lands) = f := rfl

theorem inclusion_cancel {P : T.Request → Prop}
    {f g : Interaction.Signature.Hom S (restrict T P)}
    (h : (inclusion P).comp f = (inclusion P).comp g) : f = g :=
  Proofs.Semantics.TrackA.Interface.Signature.inclusion_cancel h

/-- A translation has a unique lift exactly when all its requests lie in the sub-interface. -/
theorem factors_iff (P : T.Request → Prop) (f : Interaction.Signature.Hom S T) :
    (∃! g : Interaction.Signature.Hom S (restrict T P), (inclusion P).comp g = f) ↔
      ∀ q, P (f.request q) :=
  Proofs.Semantics.TrackA.Interface.Signature.factors_iff P f

@[simp] theorem copair_inl (f : Interaction.Signature.Hom S U)
    (g : Interaction.Signature.Hom T U) : (copair f g).comp (inl S T) = f := rfl

@[simp] theorem copair_inr (f : Interaction.Signature.Hom S U)
    (g : Interaction.Signature.Hom T U) : (copair f g).comp (inr S T) = g := rfl

/-- Together with the two injection equations, this is the coproduct universal property. -/
theorem copair_eta (h : Interaction.Signature.Hom (sum S T) U) :
    copair (h.comp (inl S T)) (h.comp (inr S T)) = h :=
  Proofs.Semantics.TrackA.Interface.Signature.copair_eta h

end Signature

namespace Renaming

@[simp] theorem id_toHom : (id S).toHom = Interaction.Signature.Hom.id S := rfl

theorem comp_toHom (f : Renaming S T) (g : Renaming T U) :
    (g.comp f).toHom = g.toHom.comp f.toHom := rfl

@[simp] theorem symm_comp_hom (f : Renaming S T) :
    f.symm.toHom.comp f.toHom = Interaction.Signature.Hom.id S :=
  Proofs.Semantics.TrackA.Interface.Renaming.symm_comp_hom f

@[simp] theorem comp_symm_hom (f : Renaming S T) :
    f.toHom.comp f.symm.toHom = Interaction.Signature.Hom.id T :=
  Proofs.Semantics.TrackA.Interface.Renaming.comp_symm_hom f

end Renaming

namespace Coalgebra

variable {B : Interaction.Signature.{b,c}} {A : Type a} {X : Type s}
variable {c : Interaction.Coalgebra S B A X} {x : X}

@[simp] theorem relabel_id (d : Interaction.Coalgebra S B A X) :
    relabel (Interaction.Signature.Hom.id S) d = d :=
  funext fun x => Node.relabel_id (d x)

theorem relabel_comp (f : Interaction.Signature.Hom S T) (g : Interaction.Signature.Hom T U)
    (d : Interaction.Coalgebra S B A X) :
    relabel (g.comp f) d = relabel g (relabel f d) :=
  funext fun x => Node.relabel_comp f g (d x)

/-- Renaming and then undoing it recovers the original unfolding. -/
@[simp] theorem relabel_rename_symm (f : Renaming S T) (d : Interaction.Coalgebra S B A X) :
    relabel f.symm.toHom (relabel f.toHom d) = d := by
  rw [← relabel_comp, Renaming.symm_comp_hom, relabel_id]

theorem extend_vis {q : S.Request} {next : S.Response q → X} (layer : c x = .vis q next) :
    extend T c x = .vis (.inl q) (fun r => next r.down) := by
  simp [extend, relabel, layer, Node.relabel, Signature.inl]

theorem relabel_extend (f : Interaction.Signature.Hom S U) (g : Interaction.Signature.Hom T U)
    (d : Interaction.Coalgebra S B A X) :
    relabel (Signature.copair f g) (extend T d) = relabel f d := by
  rw [extend, ← relabel_comp, Signature.copair_inl]

theorem hide_vis (P : S.Request → Prop) [DecidablePred P] (policy : Policy S P X)
    (refusal : A) {q : S.Request} {next : S.Response q → X}
    (layer : c x = .vis q next) (visible : P q) :
    hide P policy refusal c x = .vis ⟨q, visible⟩ next :=
  Proofs.Semantics.TrackA.Interface.Coalgebra.hide_vis P policy refusal layer visible

theorem hide_reply (P : S.Request → Prop) [DecidablePred P] (policy : Policy S P X)
    (refusal : A) {q : S.Request} {next : S.Response q → X}
    (layer : c x = .vis q next) (hidden : ¬P q) {reply : S.Response q}
    (answers : policy x q hidden = some reply) :
    hide P policy refusal c x = .tau (next reply) :=
  Proofs.Semantics.TrackA.Interface.Coalgebra.hide_reply P policy refusal layer hidden answers

theorem hide_refuse (P : S.Request → Prop) [DecidablePred P] (policy : Policy S P X)
    (refusal : A) {q : S.Request} {next : S.Response q → X}
    (layer : c x = .vis q next) (hidden : ¬P q) (refuses : policy x q hidden = none) :
    hide P policy refusal c x = .ret refusal :=
  Proofs.Semantics.TrackA.Interface.Coalgebra.hide_refuse P policy refusal layer hidden refuses

theorem restrict_refuse (P : S.Request → Prop) [DecidablePred P] (refusal : A)
    {q : S.Request} {next : S.Response q → X} (layer : c x = .vis q next) (hidden : ¬P q) :
    restrict P refusal c x = .ret refusal :=
  hide_refuse P (fun _ _ _ => none) refusal layer hidden rfl

/-- The entire observation set continues from the successor for the policy's typed reply. -/
theorem observes_hide_reply (P : S.Request → Prop) [DecidablePred P] (policy : Policy S P X)
    (refusal : A) {q : S.Request} {next : S.Response q → X}
    (layer : c x = .vis q next) (hidden : ¬P q) {reply : S.Response q}
    (answers : policy x q hidden = some reply) :
    (hide P policy refusal c).observes x = (hide P policy refusal c).observes (next reply) :=
  Interaction.Coalgebra.observes_tau (hide_reply P policy refusal layer hidden answers)

/-- A refusal has only the empty trace with the chosen terminal result. -/
theorem observes_hide_refuse (P : S.Request → Prop) [DecidablePred P] (policy : Policy S P X)
    (refusal : A) {q : S.Request} {next : S.Response q → X}
    (layer : c x = .vis q next) (hidden : ¬P q) (refuses : policy x q hidden = none) :
    (hide P policy refusal c).observes x = {Interaction.Trace.finite [] (.returned refusal)} :=
  Proofs.Semantics.TrackA.Interface.Coalgebra.observes_ret
    (hide_refuse P policy refusal layer hidden refuses)

/-- Repeatedly answering a hidden self-loop yields silent divergence. -/
theorem observes_hide_loop (P : S.Request → Prop) [DecidablePred P] (policy : Policy S P X)
    (refusal : A) {q : S.Request} {next : S.Response q → X}
    (layer : c x = .vis q next) (hidden : ¬P q) {reply : S.Response q}
    (answers : policy x q hidden = some reply) (loop : next reply = x) :
    Interaction.Trace.finite [] .diverge ∈ (hide P policy refusal c).observes x :=
  Interaction.Coalgebra.observes_silent_loop
    ((hide_reply P policy refusal layer hidden answers).trans (congrArg Node.tau loop))

/-- Every request of an included implementation is visible, regardless of the hidden policy. -/
theorem hide_relabel_inclusion (P : S.Request → Prop) [DecidablePred P] (policy : Policy S P X)
    (refusal : A) (d : Interaction.Coalgebra (Signature.restrict S P) B A X) :
    hide P policy refusal (relabel (Signature.inclusion P) d) = d :=
  Proofs.Semantics.TrackA.Interface.Coalgebra.hide_relabel_inclusion P policy refusal d

/-- Nested hiding agrees with one pass when visibility decreases and both
stages use the same refusal result. The combined policy dispatches by the first
stage at which a request is hidden. -/
theorem hide_staged {P Q : S.Request → Prop} [decP : DecidablePred P] [DecidablePred Q]
    (subset : ∀ q, P q → Q q) (first : Policy S Q X)
    (second : Policy (Signature.restrict S Q) (fun q => P q.val) X)
    (refusal : A) (d : Interaction.Coalgebra S B A X) :
    relabel (Renaming.flatten subset).toHom
        (hide (fun q : (Signature.restrict S Q).Request => P q.val)
          (dec := fun q => decP q.val) second refusal
          (hide Q first refusal d)) =
      hide P (Policy.staged first second) refusal d :=
  Proofs.Semantics.TrackA.Interface.Coalgebra.hide_staged subset first second refusal d

end Coalgebra
end Silmaril.Semantics.TrackA.Interface
