module

public import Silmaril.Semantics.ConcurrentTrace.Occurrences.Observations.Conflict.Defs
public import Mathlib.Data.Finset.Image

/-! # Observations of finite occurrence posets -/

@[expose] public section

namespace Silmaril.Semantics.ConcurrentTrace.OccurrencePoset

universe u v a

variable {T : Type u} {E : Type v} {Addr : Type a}

/-- A selection of individual event occurrences that are pairwise concurrent. -/
def EventAntichain (p : OccurrencePoset T E) (s : Finset (Fin p.size)) : Prop :=
  (∀ i ∈ s, ∃ t e, p.label i = .event t e) ∧ (s : Set (Fin p.size)).Pairwise p.Concurrent

/-- A nonempty ordered subsequence of one thread's events, with no sync
among the selected occurrences. The subsequence may skip occurrences. -/
def ThreadBlock (p : OccurrencePoset T E) (t : T) (block : List (Fin p.size)) : Prop :=
  block ≠ [] ∧ (∀ i ∈ block, ∃ e, p.label i = .event t e) ∧ block.Pairwise p.before

/-- A finite family of blocks with pairwise concurrent cross-block occurrences. -/
def ThreadBlockFamily (p : OccurrencePoset T E) {n : Nat} (threads : Fin n → T)
    (blocks : Fin n → List (Fin p.size)) : Prop :=
  (∀ k, p.ThreadBlock (threads k) (blocks k)) ∧
    ∀ ⦃k l⦄, k ≠ l → ∀ i ∈ blocks k, ∀ j ∈ blocks l, p.Concurrent i j

/-- A nonempty selection of occurrences, including syncs, with its induced
strict order. It can skip occurrences even along causal chains. -/
def Fragment (p : OccurrencePoset T E) (s : Finset (Fin p.size)) : Prop :=
  s.Nonempty

/-- Restrict the ambient causal order to a fragment. -/
def fragmentBefore (p : OccurrencePoset T E) {s : Finset (Fin p.size)}
    (i j : {x // x ∈ s}) : Prop :=
  p.before i.val j.val

/-- A finite family of fragments with pairwise concurrent cross-fragment
occurrences. Each fragment retains the ambient order on its own carrier. -/
def FragmentFamily (p : OccurrencePoset T E) {n : Nat}
    (fragments : Fin n → Finset (Fin p.size)) : Prop :=
  (∀ k, p.Fragment (fragments k)) ∧
    ∀ ⦃k l⦄, k ≠ l → ∀ i ∈ fragments k, ∀ j ∈ fragments l, p.Concurrent i j

/-- The abstract addresses touched by one occurrence. A sync contributes no addresses. -/
def touched (p : OccurrencePoset T E) (touches : T → E → Set Addr) (i : Fin p.size) : Set Addr :=
  eventFootprint touches (p.label i)

/-- The overlap of two concurrent event footprints. -/
def raceAt (p : OccurrencePoset T E) (touches : T → E → Set Addr) (i j : Fin p.size) :
    Set Addr :=
  p.conflictAt (anyTouchPolicy touches) i j

/-- All addresses observed in a concurrent overlap. -/
def raceAddresses (p : OccurrencePoset T E) (touches : T → E → Set Addr) : Set Addr :=
  p.conflictAddresses (anyTouchPolicy touches)

end Silmaril.Semantics.ConcurrentTrace.OccurrencePoset
