module

import Silmaril.Semantics.TrackA.Interface.Thms
import Silmaril.Semantics.TrackA.Interaction.UB.Thms

namespace Silmaril.Semantics.TrackA.Interface.Regression

open Interaction (Signature Coalgebra Trace)
open Interface (Renaming)

private def Public : Signature := ⟨Bool, fun _ => Unit⟩
private def Private : Signature := ⟨Unit, fun _ => Bool⟩
private abbrev Combined := Interface.Signature.sum Public Private

private def visible : Combined.Request → Prop
  | .inl _ => True
  | .inr _ => False

private instance : DecidablePred visible
  | .inl _ => isTrue trivial
  | .inr _ => isFalse id

private inductive State
  | read
  | emit (bit : Bool)
  | done (bit : Bool)

private inductive ReadError where
  | refused

private abbrev Result := Except ReadError Bool

private def refused : Result := .error .refused

private def program : Coalgebra Combined Signature.noChoice (Option Result) State
  | .read => .vis (.inr ()) fun r => .emit r.down
  | .emit bit => .vis (.inl bit) fun _ => .done bit
  | .done bit => .ret (some (.ok bit))

private def answer (bit : Bool) {X : Type} : Interface.Coalgebra.Policy Combined visible X
  | _, .inl _, _ => none
  | _, .inr _, _ => some ⟨bit⟩

private def emission (bit : Bool) : (Interface.Signature.restrict Combined visible).Exchange :=
  ⟨⟨.inl bit, trivial⟩, ⟨()⟩⟩

/-- The hidden response determines the next public request and final result. -/
private theorem hidden_reply_controls_emission (bit : Bool) :
    Trace.finite [emission bit] (.returned (some (.ok bit))) ∈
      (Interface.Coalgebra.hide visible (answer bit) (some refused) program).observes .read := by
  rw [Interface.Coalgebra.observes_hide_reply visible (answer bit) (some refused)
    (x := State.read) (q := Sum.inr ()) (next := fun r => .emit r.down) rfl id
    (reply := ⟨bit⟩) rfl]
  refine ⟨.done bit, .done bit, .cons ⟨.emit bit, .refl, ?_⟩ (.nil _), .refl, rfl⟩
  exact .vis (c := Interface.Coalgebra.hide visible (answer bit) (some refused) program)
    (x := State.emit bit) (q := (emission bit).1) (next := fun _ => State.done bit) rfl (emission bit).2

/-- Refusing the same request stops before any public exchange. -/
private theorem refusal_returns_only (result : Option Result) :
    (Interface.Coalgebra.restrict visible result program).observes .read =
    {Trace.finite [] (.returned result)} :=
  Interface.Coalgebra.observes_hide_refuse visible (fun _ _ _ => none) result
    (q := Sum.inr ()) (next := fun r => .emit r.down) rfl id rfl

private theorem refusal_at_boundary (result : Option Result) :
    Interaction.UB.atBoundary ((Interface.Coalgebra.restrict visible result program).observes .read) =
      {Interaction.UB.classify (.finite [] (.returned result))} := by
  rw [refusal_returns_only]
  simp [Interaction.UB.atBoundary]

/-- An ordinary refusal survives collapse as exactly one error trace, without a UB marker. -/
private theorem ordinary_refusal_survives_collapse :
    (Interaction.UB.collapse (Interaction.UB.atBoundary
      ((Interface.Coalgebra.restrict visible (some refused) program).observes .read))).val =
    {some (Trace.finite [] (.returned refused))} := by
  rw [refusal_at_boundary]
  exact Interaction.UB.val_collapse_of_safe _ (by simp [Interaction.UB.classify])

/-- Choosing the outer `none` as the terminal result makes the same run catastrophic. -/
private theorem deliberate_ub_collapses_to_top :
    Interaction.UB.collapse (Interaction.UB.atBoundary
      ((Interface.Coalgebra.restrict visible none program).observes .read)) = ⊤ := by
  rw [refusal_at_boundary]
  exact (Interaction.UB.collapse_eq_top_iff _).2 (by simp [Interaction.UB.classify])

private def polling : Coalgebra Combined Signature.noChoice (Option Result) Unit :=
  fun _ => .vis (.inr ()) fun _ => ()

private def pollExchange : Combined.Exchange := ⟨.inr (), ⟨true⟩⟩

private theorem visible_polling_can_exchange_forever :
    Trace.infinite (fun _ => pollExchange) ∈ polling.observes () :=
  Coalgebra.observes_visible_loop (c := polling) (q := pollExchange.1) pollExchange.2 rfl

private theorem hidden_polling_diverges : Trace.finite [] .diverge ∈
    (Interface.Coalgebra.hide visible (answer true) (some refused) polling).observes () :=
  Interface.Coalgebra.observes_hide_loop visible (answer true) (some refused)
    (q := Sum.inr ()) (next := fun _ => ()) rfl id (reply := ⟨true⟩) rfl rfl

private theorem left_injection_factors :
    ∃! f : Signature.Hom Public (Interface.Signature.restrict Combined visible),
    (Interface.Signature.inclusion visible).comp f = Interface.Signature.inl Public Private :=
  (Interface.Signature.factors_iff visible (Interface.Signature.inl Public Private)).2 fun _ => trivial

private def Source : Signature := ⟨Bool, fun | false => Unit | true => Bool⟩
private def Wire : Signature := ⟨Bool, fun | false => Bool | true => Unit⟩
private def flip : Bool ≃ Bool := ⟨Bool.not, Bool.not, Bool.not_not, Bool.not_not⟩

private def encoding : Renaming Source Wire :=
  ⟨flip, fun | false => Equiv.refl Unit | true => flip⟩

private def echo : Coalgebra Source Signature.noChoice Bool (Option Bool)
  | none => .vis true some
  | some bit => .ret bit

/-- The renamed request decodes the new reply before entering the source continuation. -/
private theorem renaming_decodes_reply :
    Interface.Coalgebra.relabel encoding.toHom echo none = .vis false (fun r => some (!r)) := rfl

private theorem renaming_round_trip : Interface.Coalgebra.relabel encoding.symm.toHom
    (Interface.Coalgebra.relabel encoding.toHom echo) = echo :=
  Interface.Coalgebra.relabel_rename_symm encoding echo

end Silmaril.Semantics.TrackA.Interface.Regression
