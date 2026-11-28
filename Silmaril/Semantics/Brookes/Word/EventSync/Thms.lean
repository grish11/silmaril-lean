module

public import Silmaril.Semantics.Brookes.Word.Thms
public import Silmaril.Semantics.ConcurrentTrace.Thms
import Silmaril.Proofs.Semantics.Brookes.Word.EventSync.Comparison

/-! # Brookes descent for the concrete event/sync alphabet -/

public section

namespace Silmaril.Semantics.Brookes.Word.EventSync

open Silmaril.Semantics.ConcurrentTrace

universe u v w

variable {T : Type u} {E : Type v} {Store : Type w}
variable {letter : Letter T E → Command Store}

/-- The finite trace monoid and Brookes's generic swap quotient identify the same words
when the latter uses the event/sync independence relation. -/
@[expose] def swapEquiv : ConcurrentTrace.Trace T E ≃ Quot (Swap (Letter.Independent (T := T) (E := E))) where
  toFun x := Quotient.liftOn x (fun w => Quot.mk _ w.toList)
    (by intro _ _ h; exact Proofs.Semantics.Brookes.Word.EventSync.swapClass_eq h)
  invFun := Quot.lift ofWord (by intro _ _ h; exact
    Proofs.Semantics.Brookes.Word.EventSync.ofWord_eq_of_swap h)
  left_inv x := Quotient.inductionOn x fun _ => rfl
  right_inv x := Quot.inductionOn x fun _ => rfl

/-- Interpret finite event/sync traces as open commands when every independent pair
commutes as a full Brookes command. -/
@[expose] def denote (h : Commutes Letter.Independent letter) : ConcurrentTrace.Trace T E → Command Store :=
  Word.lift h ∘ swapEquiv

/-- Interpret finite event/sync traces by contiguous endpoints when every independent
pair commutes at endpoints. -/
@[expose] def denoteEndpoints (h : CommutesAtEndpoints Letter.Independent letter) :
    ConcurrentTrace.Trace T E → Store → Store → Prop :=
  Word.liftEndpoints h ∘ swapEquiv

@[simp] theorem denote_ofWord (h : Commutes Letter.Independent letter)
    (word : ConcurrentTrace.Word T E) : denote h (ofWord word) = Word.eval letter word :=
  rfl

@[simp] theorem denoteEndpoints_ofWord (h : CommutesAtEndpoints Letter.Independent letter)
    (word : ConcurrentTrace.Word T E) :
    denoteEndpoints h (ofWord word) = endpoints (Word.eval letter word) :=
  rfl

/-- Endpoint observation commutes with open descent when both lifts exist. -/
theorem endpoints_denote (h : Commutes Letter.Independent letter)
    (he : CommutesAtEndpoints Letter.Independent letter) (trace : ConcurrentTrace.Trace T E) :
    endpoints (denote h trace) = denoteEndpoints he trace := by
  obtain ⟨word, rfl⟩ := ofWord_surjective trace
  rfl

/-- The open interpretation descends exactly under the open commutation hypothesis. -/
theorem exists_denote_iff :
    (∃ f : ConcurrentTrace.Trace T E → Command Store, ∀ word, f (ofWord word) = Word.eval letter word) ↔
      Commutes Letter.Independent letter :=
  ⟨fun ⟨f, hf⟩ => commutes_of_lift (f ∘ swapEquiv.symm) hf, fun h => ⟨denote h, denote_ofWord h⟩⟩

/-- The endpoint interpretation descends exactly under endpoint commutation. -/
theorem exists_denoteEndpoints_iff :
    (∃ f : ConcurrentTrace.Trace T E → Store → Store → Prop,
      ∀ word, f (ofWord word) = endpoints (Word.eval letter word)) ↔
      CommutesAtEndpoints Letter.Independent letter :=
  ⟨fun ⟨f, hf⟩ => commutesAtEndpoints_of_lift (f ∘ swapEquiv.symm) hf,
    fun h => ⟨denoteEndpoints h, denoteEndpoints_ofWord h⟩⟩

end Silmaril.Semantics.Brookes.Word.EventSync
