module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Refinement.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Refinement.Total
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Refinement.Order

/-! # Directed handled-trace inclusion at the free interpretation

For a reply policy that can replay every complete history, handled-trace
inclusion of the packed programs is the tree relation on the captured
operands. Replay reads only the completed exchanges of an observation, so
a policy that replays complete histories replays every finite observation,
including pending requests.

Acyclic terms have no silent divergence. A tree without divergence is
maximal for inclusion of observations. The tree relation, the outcome
relation and handled-trace inclusion at such a policy therefore all
coincide with native equality on this fragment, and the hom order on the
image of the semantic functor is discrete.

The collapse of the tree relation uses only the absence of divergence. The
collapse of the outcome relation also uses that every primitive of the
finite structural signature has an inhabited reply type.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free

open CategoryTheory Silmaril.Elgot.ITree
open Region (packedExitType)
open Reverse (CheckedTable)
open Isotope.Semantics (BoundEnv)
open LetCase.LocallyNameless (Derivation Equiv)
open LetCase.Structural.Finite (Context StructuralContext)
open LetCase.Structural.Reply (Γ₀)
open LetCase (HandledTrace.Program HandledTrace.Arrow)
open LetSeq.StraightLine.Structural (Log)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

universe s

/-! ## Trees without divergence -/

section Trees

variable {E : Type → Type} {X Y : Type 1}

theorem total_bind {t : Tree E X} {k : X → Tree E Y} (first : Total t) (rest : ∀ x, Total (k x)) :
    Total (t >>= k) :=
  total_bind_proof first rest

/-- A tree without divergence is maximal for inclusion of observations.
The comparison at a request with no replies needs only the request. -/
theorem eq_of_total_traceLE {t u : Tree E X} (total : Total t) (below : TraceLE t u) : t = u :=
  eq_of_total_traceLE_proof total below

end Trees

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ] {State : Type s} {X Y : Type 1}

/-- Acyclic terms have no divergence at the free interpretation. -/
theorem total_denote {n : Nat} {γ : Context n} {t : LetCase.LocallyNameless.Tm Empty Φ n} {A : Ty Empty}
    (d : Derivation Φ Γ₀ γ t A) (ρ : BoundEnv Val γ) :
    Total (d.denote Val (model Φ) (fun x => x.elim) ρ) :=
  total_denote_proof d ρ

/-- Every reply type of the signature is inhabited, so a tree without
divergence has a complete history. -/
theorem exists_history {t : Tree (Events Φ) X} (total : Total t) :
    ∃ (log : Log Empty Φ) (y : X), HasTrace t (history log y) :=
  exists_history_proof total

/-- With inhabited reply types, a tree without divergence is already
maximal for inclusion of complete histories. -/
theorem eq_of_total_histories {t u : Tree (Events Φ) X} (total : Total t)
    (below : ∀ (log : Log Empty Φ) (y : X), HasTrace t (history log y) → HasTrace u (history log y)) :
    t = u :=
  eq_of_total_histories_proof total below

/-! ## Replay reads only completed exchanges -/

theorem replay_history_iff (policy : Handler State (Events Φ)) (p : Trace (Events Φ) X) (y : Y)
    (state : State) : Replay policy state (history (exchanges p) y) ↔ Replay policy state p :=
  replay_history_iff_proof policy p y state

/-- Replaying every complete history is the same as replaying every finite
observation, whatever its end: a prefix, a pending request or a return. -/
theorem exposes_iff {policy : Handler State (Events Φ)} :
    Exposes policy ↔ ∀ {X : Type 1} (p : Trace (Events Φ) X), ∃ state, Replay policy state p :=
  ⟨fun exposes _ p => replay_of_exposes_proof exposes p, fun all _ log result => all (history log result)⟩

/-- At such a policy, handled-trace inclusion from every state is inclusion
of all finite observations. -/
theorem handled_iff_traceLE {policy : Handler State (Events Φ)} (exposes : Exposes policy)
    (t u : Tree (Events Φ) X) : (∀ state, HandledTraceLE policy state t u) ↔ TraceLE t u :=
  handled_iff_traceLE_proof exposes t u

/-! ## The directed bridge on captured operands -/

variable {d : Nat} {β : Context d} {A B : Ty Empty}

/-- The tree relation gives handled-trace inclusion of the packed programs
at every policy. -/
theorem refines_of_treeRefines (policy : Handler State (Events Φ)) {a b : Operand Φ (β.snoc A) B}
    (tree : TreeRefines a b) : HandledTrace.Program.Refines (model Φ) policy (pack β a) (pack β b) :=
  refines_of_treeRefines_proof policy tree

/-- Handled-trace inclusion of the packed programs gives the tree relation
when the policy replays every complete history. -/
theorem treeRefines_of_refines {policy : Handler State (Events Φ)} (exposes : Exposes policy)
    {a b : Operand Φ (β.snoc A) B}
    (refines : HandledTrace.Program.Refines (model Φ) policy (pack β a) (pack β b)) : TreeRefines a b :=
  treeRefines_of_refines_proof exposes refines

theorem refines_iff_treeRefines {policy : Handler State (Events Φ)} (exposes : Exposes policy)
    (a b : Operand Φ (β.snoc A) B) :
    HandledTrace.Program.Refines (model Φ) policy (pack β a) (pack β b) ↔ TreeRefines a b :=
  ⟨treeRefines_of_refines exposes, refines_of_treeRefines policy⟩

/-! ## The order collapses on acyclic terms -/

/-- The tree relation is native equality. One direction of inclusion
already forces the other. -/
theorem treeRefines_iff_equiv (input : StructuralContext β) (a b : Operand Φ (β.snoc A) B) :
    TreeRefines a b ↔ Equiv false Γ₀ (β.snoc A) a.1 b.1 B :=
  ⟨equiv_of_treeRefines_proof input, treeRefines_of_equiv_proof⟩

/-- Inclusion of ordered complete outcomes is native equality. This uses
the inhabited reply types of the signature. -/
theorem outcomeRefines_iff_equiv (input : StructuralContext β) (a b : Operand Φ (β.snoc A) B) :
    OutcomeRefines a b ↔ Equiv false Γ₀ (β.snoc A) a.1 b.1 B :=
  ⟨equiv_of_outcomeRefines_proof input, outcomeRefines_of_equiv_proof⟩

/-- One direction of handled-trace inclusion of the packed programs, at a
policy that replays every complete history, is native equality. -/
theorem refines_iff_equiv (input : StructuralContext β) {policy : Handler State (Events Φ)}
    (exposes : Exposes policy) (a b : Operand Φ (β.snoc A) B) :
    HandledTrace.Program.Refines (model Φ) policy (pack β a) (pack β b) ↔
      Equiv false Γ₀ (β.snoc A) a.1 b.1 B :=
  (refines_iff_treeRefines exposes a b).trans (treeRefines_iff_equiv input a b)

/-! ## On native classes and written graphs -/

variable {I J : LCtx (Ty Empty)}

/-- The tree relation does not depend on the native representatives. -/
theorem treeRefines_congr {a a' b b' : Operand Φ (β.snoc A) B}
    (left : Equiv false Γ₀ (β.snoc A) a.1 a'.1 B) (right : Equiv false Γ₀ (β.snoc A) b.1 b'.1 B) :
    TreeRefines a b ↔ TreeRefines a' b' :=
  treeRefines_congr_proof left right

/-- The tree relation on native equation classes. -/
def TreeLE (p q : Case.Hom Φ β I J) : Prop :=
  Quotient.liftOn₂ p q TreeRefines fun _ _ _ _ left right => propext (treeRefines_congr left right)

@[simp] theorem treeLE_mk (a b : Operand Φ (β.snoc (packedExitType I)) (packedExitType J)) :
    TreeLE (Quotient.mk _ a) (Quotient.mk _ b) ↔ TreeRefines a b :=
  Iff.rfl

theorem treeLE_iff_eq (input : StructuralContext β) (p q : Case.Hom Φ β I J) : TreeLE p q ↔ p = q :=
  Quotient.inductionOn₂ p q fun a b =>
    (treeRefines_iff_equiv input a b).trans ⟨fun h => Quotient.sound h, Quotient.exact⟩

/-- The tree relation gives the hom order of the handled-trace category
at every policy. -/
theorem handledFunctor_map_le_of_treeLE (input : StructuralContext β) (policy : Handler State (Events Φ))
    {X Y : Case.Interface Φ β input} {p q : X ⟶ Y} (tree : TreeLE p q) :
    (handledFunctor (model Φ) policy input).map p ≤ (handledFunctor (model Φ) policy input).map q := by
  revert tree
  exact Quotient.inductionOn₂ p q fun a b tree => refines_of_treeRefines policy tree

/-- At a policy that replays every complete history, the hom order of the
handled-trace category is the tree relation on native classes. -/
theorem handledFunctor_map_le_iff (input : StructuralContext β) {policy : Handler State (Events Φ)}
    (exposes : Exposes policy) {X Y : Case.Interface Φ β input} (p q : X ⟶ Y) :
    (handledFunctor (model Φ) policy input).map p ≤ (handledFunctor (model Φ) policy input).map q ↔
      TreeLE p q :=
  Quotient.inductionOn₂ p q fun a b => refines_iff_treeRefines exposes a b

/-- The hom order on the image of the semantic functor is discrete. -/
theorem handledFunctor_map_le_iff_eq (input : StructuralContext β) {policy : Handler State (Events Φ)}
    (exposes : Exposes policy) {X Y : Case.Interface Φ β input} (p q : X ⟶ Y) :
    (handledFunctor (model Φ) policy input).map p ≤ (handledFunctor (model Φ) policy input).map q ↔
      p = q :=
  (handledFunctor_map_le_iff input exposes p q).trans (treeLE_iff_eq input p q)

/-- For written graphs, the hom order after the actual emitter is the tree
relation on the emitted classes. -/
theorem ssaHandledFunctor_map_le_iff (input : StructuralContext β) {policy : Handler State (Events Φ)}
    (exposes : Exposes policy) {X Y : Interface Φ β input} (p q : X ⟶ Y) :
    (ssaHandledFunctor (model Φ) policy input).map p ≤ (ssaHandledFunctor (model Φ) policy input).map q ↔
      TreeLE ((emitFunctor input).map p) ((emitFunctor input).map q) :=
  handledFunctor_map_le_iff input exposes ((emitFunctor input).map p) ((emitFunctor input).map q)

/-- On written representatives, the order compares the emitted operands. -/
theorem ssaHandledFunctor_map_le_mk (input : StructuralContext β) {policy : Handler State (Events Φ)}
    (exposes : Exposes policy) {X Y : Interface Φ β input}
    (p q : CheckedTable Φ (β.snoc (packedExitType X.exits)) Y.exits) :
    (ssaHandledFunctor (model Φ) policy input).map (X := X) (Y := Y) (Quotient.mk _ p) ≤
        (ssaHandledFunctor (model Φ) policy input).map (X := X) (Y := Y) (Quotient.mk _ q) ↔
      TreeRefines p.toLetCase q.toLetCase := by
  rw [ssaHandledFunctor_map_mk, ssaHandledFunctor_map_mk]
  exact refines_iff_treeRefines exposes p.toLetCase q.toLetCase

/-- The comparison commutes with checked readback: the tree relation on
native classes is the hom order of the written graphs read back from them. -/
theorem treeLE_iff_readback_le (input : StructuralContext β) {policy : Handler State (Events Φ)}
    (exposes : Exposes policy) {X Y : Case.Interface Φ β input} (p q : X ⟶ Y) :
    TreeLE p q ↔
      (ssaHandledFunctor (model Φ) policy input).map ((readbackFunctor input).map p) ≤
        (ssaHandledFunctor (model Φ) policy input).map ((readbackFunctor input).map q) := by
  have written := ssaHandledFunctor_map_le_iff input exposes
    ((readbackFunctor input).map p) ((readbackFunctor input).map q)
  rw [emitFunctor_map_readbackFunctor_map, emitFunctor_map_readbackFunctor_map] at written
  exact written.symm

/-- The hom order on the image of written graphs is discrete as well. -/
theorem ssaHandledFunctor_map_le_iff_eq (input : StructuralContext β) {policy : Handler State (Events Φ)}
    (exposes : Exposes policy) {X Y : Interface Φ β input} (p q : X ⟶ Y) :
    (ssaHandledFunctor (model Φ) policy input).map p ≤ (ssaHandledFunctor (model Φ) policy input).map q ↔
      p = q :=
  ⟨fun below => by
      have emitted := (handledFunctor_map_le_iff_eq input exposes
        ((emitFunctor input).map p) ((emitFunctor input).map q)).mp below
      rw [← readbackFunctor_map_emitFunctor_map input p, emitted, readbackFunctor_map_emitFunctor_map],
    fun same => same ▸ le_refl _⟩

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free
