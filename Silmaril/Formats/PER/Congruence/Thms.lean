module
public import Silmaril.Formats.PER.Congruence.Defs
import Silmaril.Proofs.Formats.PER.Congruence.Basic

@[expose] public section
namespace Silmaril.Formats.PER
variable {α : Type}

instance : InfSet (PER α) := ⟨fun family => PER.iInf fun member : family => member.val⟩

theorem sInf_isGLB (family : Set (PER α)) : IsGLB family (sInf family) :=
  Proofs.Formats.PER.Congruence.sInf_isGLB family

instance : CompleteLattice (PER α) :=
  completeLatticeOfInf _ sInf_isGLB

/-- Least PER containing an arbitrary relation; arbitrary joins close the union this way. -/
def hull (rel : α → α → Prop) : PER α := sInf {S | ∀ ⦃left right⦄, rel left right → S.rel left right}

theorem sSup_eq_hull (family : Set (PER α)) :
    sSup family = hull (fun left right => ∃ R ∈ family, R.rel left right) := by
  change sInf (upperBounds family) = _
  congr 1
  ext R
  exact ⟨fun h _ _ ⟨S, hs, rel⟩ => h hs rel, fun h S hs _ _ rel => h ⟨S, hs, rel⟩⟩

@[simp] theorem bot_eq_empty : (⊥ : PER α) = empty α :=
  le_antisymm (bot_le) (fun _ _ h => h.elim)

namespace Constructors
variable (C : Constructors α) {R S E : PER α}

theorem le_generated (R : PER α) : R ≤ C.generated R := fun _ _ h target => target.property.1 h

theorem generated_closed (R : PER α) : C.Closed (C.generated R) :=
  Proofs.Formats.PER.Congruence.generated_closed C R

theorem generated_le (h : R ≤ S) (closed : C.Closed S) : C.generated R ≤ S :=
  fun _ _ hr => hr ⟨S, h, closed⟩

def closureOperator : ClosureOperator (PER α) :=
  ClosureOperator.ofPred C.generated C.Closed C.le_generated C.generated_closed (fun _ _ => C.generated_le)

/-- With inclusion as the order, meets are intersections and joins close the underlying PER joins. -/
def Congruent := C.closureOperator.Closeds

instance : CompleteLattice C.Congruent :=
  C.closureOperator.gi.liftCompleteLattice

theorem congruent_sSup (family : Set C.Congruent) :
    (sSup family).val = C.generated (sSup (Subtype.val '' family)) := rfl

theorem congruent_sInf (family : Set C.Congruent) :
    (sInf family).val = sInf (Subtype.val '' family) := rfl

theorem generated_eq (closed : C.Closed R) : C.generated R = R :=
  C.closureOperator.isClosed_iff.mp closed

theorem generated_mono : Monotone C.generated := C.closureOperator.monotone

@[simp] theorem generated_idem (R : PER α) : C.generated (C.generated R) = C.generated R :=
  C.closureOperator.idempotent R

theorem none_closed (R : PER α) : (Constructors.none α).Closed R := fun shape => shape.elim

theorem upper_support (h : C.upper R E) {left right : α} (related : E.rel left right) :
    (C.generated R).Dom left ∧ (C.generated R).Dom right :=
  ⟨(C.generated R).dom_left (h related), (C.generated R).dom_right (h related)⟩

/-- For a closed seed, the upper condition gives semantic agreement and original validity.
Without closedness, only support in the generated PER is guaranteed. -/
theorem upper_sound (h : C.upper R E) (closed : C.Closed R) : E ≤ R := by
  simpa only [upper, C.generated_eq closed] using h

theorem syntaxCompatible_eq (h : C.SyntaxCompatible R E) (closed : C.Closed R) : E = R :=
  le_antisymm (C.upper_sound h.2.1 closed) h.1

theorem syntaxCompatible_valid (h : C.SyntaxCompatible R E) (closed : C.Closed R) (value : α) :
    R.Dom value := C.upper_sound h.2.1 closed (h.2.2 value)

theorem map_generated {β : Type} (D : Constructors β) (f : α → β) {S : PER β}
    (seed : R ≤ S.pull f) (closed : C.Closed ((D.generated S).pull f)) :
    C.generated R ≤ (D.generated S).pull f :=
  Proofs.Formats.PER.Congruence.map_generated C D f seed closed

end Constructors
end Silmaril.Formats.PER
