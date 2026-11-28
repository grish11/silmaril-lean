module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Satisfaction

/-! # Satisfaction squares for captured sentences over handled-trace models

The sentences are the existing ranked, grammar and LetCase equations. The
models are the existing handled-trace models over the free requests. The
existing emission and readback of sentences are corridors with the identity
on models. On the endpoints of the written and native captured categories,
satisfaction is the hom order of the handled-trace category under the
semantic functors.

A model that replays every complete history from an initial state
satisfies a directed captured sentence exactly when its two sides are
natively equal. The model that admits every reply is of this kind. A
model with one fixed policy may satisfy more.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open CategoryTheory Silmaril.Elgot.ITree
open Silmaril.Logic.Institution (Room)
open Silmaril.Logic.ITree (Model)
open Silmaril.Logic.ITree.TraceInstitution (Sat allRepliesModel)
open Silmaril.Isotope.Institution.Acyclic (CaseEquation)
open Silmaril.Isotope.Institution.Acyclic.Captured (GrammarEquation RankedEquation grammarCase readGrammar
  numberGrammar grammarCase_roundTrip)
open Region (packedExitType)
open Reverse (CheckedTable)
open Isotope.Semantics (BoundEnv)
open LetCase.LocallyNameless (Equiv)
open LetCase.Structural.Finite (Context StructuralContext)
open LetCase.Structural.Reply (Γ₀)
open LetCase (HandledTrace.Program HandledTrace.Arrow)
open Free
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

/-! ## Replay and packing -/

section Trees

universe u v w

variable {E : Type u → Type u} {X Y : Type v} {State : Type w}

/-- Replay does not read returned values. -/
theorem replay_map (step : Handler State E) (g : X → Y) (p : Trace E X) (state : State) :
    Replay step state (p.map g) ↔ Replay step state p :=
  replay_map_proof step g p state

/-- Handled-trace inclusion is unchanged by an injective pure return map. -/
theorem handled_bind_pure_iff (step : Handler State E) {g : X → Y} (injective : Function.Injective g)
    (state : State) (t u : Tree E X) :
    HandledTraceLE step state (t >>= fun x => pure (g x)) (u >>= fun x => pure (g x)) ↔
      HandledTraceLE step state t u :=
  handled_bind_pure_iff_proof step injective state t u

end Trees

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ] {M : HandledModel Φ}

/-! ## Satisfaction of one refinement sentence -/

/-- The existing trace sentence holds exactly when handled-trace inclusion
holds from every initial state. -/
theorem sat_refinement_iff {n : Nat} {γ : Context n} {B : Ty Empty} (a b : Operand Φ γ B)
    (ρ : BoundEnv Val γ) :
    Sat M (refinement a b ρ) ↔ ∀ x, M.initial x → HandledTraceLE M.step x
      (a.2.denote Val (model Φ) (fun x => x.elim) ρ) (b.2.denote Val (model Φ) (fun x => x.elim) ρ) :=
  sat_refinement_iff_proof a b ρ

/-- In a model that replays every complete history from an initial state,
the sentence is inclusion of all finite observations. -/
theorem sat_refinement_of_exposing (exposing : Exposing M) {n : Nat} {γ : Context n} {B : Ty Empty}
    (a b : Operand Φ γ B) (ρ : BoundEnv Val γ) :
    Sat M (refinement a b ρ) ↔ TraceLE (a.2.denote Val (model Φ) (fun x => x.elim) ρ)
      (b.2.denote Val (model Φ) (fun x => x.elim) ρ) :=
  sat_refinement_of_exposing_proof exposing a b ρ

variable {d : Nat} {β : Context d} {A B : Ty Empty} {I J : LCtx (Ty Empty)}

/-! ## Captured sentences -/

/-- Satisfaction does not depend on the native representatives. -/
theorem satLe_congr {a a' b b' : Operand Φ (β.snoc A) B}
    (left : Equiv false Γ₀ (β.snoc A) a.1 a'.1 B) (right : Equiv false Γ₀ (β.snoc A) b.1 b'.1 B) :
    SatLe M (captured a b) ↔ SatLe M (captured a' b') :=
  satLe_congr_proof left right

/-- Natively equal operands satisfy the directed sentence in every model. -/
theorem satLe_of_equiv {a b : Operand Φ (β.snoc A) B} (h : Equiv false Γ₀ (β.snoc A) a.1 b.1 B) :
    SatLe M (captured a b) :=
  (satLe_congr (.refl a.2.toHasType) h).mp (satLe_refl_proof a)

/-- With every state initial, satisfaction is handled-trace inclusion of
the packed programs at the model's policy. -/
theorem satLe_iff_refines {State : Type} (policy : Handler State (Events Φ)) (a b : Operand Φ (β.snoc A) B) :
    SatLe (⟨State, fun _ => True, policy⟩ : HandledModel Φ) (captured a b) ↔
      HandledTrace.Program.Refines (model Φ) policy (pack β a) (pack β b) :=
  satLe_iff_refines_proof policy a b

/-! ## Models that replay every history -/

theorem exposing_of_exposes {State : Type} {policy : Handler State (Events Φ)} (exposes : Exposes policy) :
    Exposing (⟨State, fun _ => True, policy⟩ : HandledModel Φ) :=
  exposing_of_exposes_proof exposes

/-- The existing model that admits every typed reply. -/
theorem allReplies_exposing : Exposing (allRepliesModel (events Φ) : HandledModel Φ) :=
  allReplies_exposing_proof

theorem satLe_iff_treeRefines (exposing : Exposing M) (a b : Operand Φ (β.snoc A) B) :
    SatLe M (captured a b) ↔ TreeRefines a b :=
  satLe_iff_treeRefines_proof exposing a b

/-- In such a model over a structural older context, a directed captured
sentence holds exactly when its sides are natively equal. -/
theorem satLe_iff_equiv (input : StructuralContext β) (exposing : Exposing M) (a b : Operand Φ (β.snoc A) B) :
    SatLe M (captured a b) ↔ Equiv false Γ₀ (β.snoc A) a.1 b.1 B :=
  (satLe_iff_treeRefines exposing a b).trans (treeRefines_iff_equiv input a b)

/-- A directed captured sentence is valid in all handled models exactly
when its sides are natively equal. -/
theorem valid_iff_equiv (input : StructuralContext β) (a b : Operand Φ (β.snoc A) B) :
    (∀ M : HandledModel Φ, SatLe M (captured a b)) ↔ Equiv false Γ₀ (β.snoc A) a.1 b.1 B :=
  ⟨fun valid => (satLe_iff_equiv input allReplies_exposing a b).mp (valid _), fun h _ => satLe_of_equiv h⟩

/-! ## Emission and readback of sentences -/

/-- The existing emission of a pair of written graphs is the pair of their
emitted operands. -/
theorem grammarCase_read_rankedOf (p q : CheckedTable Φ (β.snoc (packedExitType I)) J) :
    grammarCase (readGrammar (rankedOf p q)) = captured p.toLetCase q.toLetCase :=
  ranked_endpoint_proof p q

/-- The existing numbering of the readback witnesses is the pair of graphs
built by the checked readback. -/
theorem numberGrammar_grammarOf (h : J ≠ [])
    (a b : Operand Φ (β.snoc (packedExitType I)) (packedExitType J)) :
    numberGrammar (grammarOf h a b) =
      rankedOf (CheckedTable.ofLetCase h a.2) (CheckedTable.ofLetCase h b.2) :=
  number_endpoint_proof h a b

/-- Rendering grammar witnesses to LetCase, with the same models. -/
noncomputable def grammarCaseCorridor (Φ : Type) [LetCase.Structural.Finite.Signature Φ] :
    grammarRoom Φ ⟶ caseRoom Φ :=
  ⟨grammarCase, 𝟭 _, fun _ _ => Iff.rfl⟩

/-- Emission of ranked sentences to grammar witnesses, with the same models. -/
noncomputable def readCorridor (Φ : Type) [LetCase.Structural.Finite.Signature Φ] :
    rankedRoom Φ ⟶ grammarRoom Φ :=
  ⟨readGrammar, 𝟭 _, fun _ _ => Iff.rfl⟩

/-- Readback of grammar witnesses to ranked sentences, with the same models. -/
noncomputable def numberCorridor (Φ : Type) [LetCase.Structural.Finite.Signature Φ] :
    grammarRoom Φ ⟶ rankedRoom Φ :=
  ⟨numberGrammar, 𝟭 _, fun M e => Iff.of_eq (congrArg (SatLe M.as) (grammarCase_roundTrip e))⟩

/-- Emitting after numbering does not change satisfaction of a grammar sentence. -/
theorem sat_read_number (N : (grammarRoom Φ).Mod) (e : GrammarEquation (sig Φ)) :
    (grammarRoom Φ).Sat N (readGrammar (numberGrammar e)) ↔ (grammarRoom Φ).Sat N e :=
  (numberCorridor Φ).sat N e

/-- Numbering after emitting does not change satisfaction of a ranked sentence. -/
theorem sat_number_read (N : (rankedRoom Φ).Mod) (e : RankedEquation (sig Φ)) :
    (rankedRoom Φ).Sat N (numberGrammar (readGrammar e)) ↔ (rankedRoom Φ).Sat N e :=
  (numberCorridor Φ).sat N (readGrammar e)

/-- The checked readback of a pair of captured operands, as a ranked
sentence, holds exactly when the LetCase sentence on the operands holds. -/
theorem sat_readback (h : J ≠ []) (a b : Operand Φ (β.snoc (packedExitType I)) (packedExitType J))
    (N : (caseRoom Φ).Mod) :
    (rankedRoom Φ).Sat N (numberGrammar (grammarOf h a b)) ↔ (caseRoom Φ).Sat N (captured a b) :=
  sat_readback_proof h a b

/-! ## The hom order of the semantic functors -/

/-- On native classes, the hom order under the semantic functor is
satisfaction of the LetCase sentence in the model of that policy. -/
theorem handledFunctor_map_le_iff_sat (input : StructuralContext β) {State : Type}
    (policy : Handler State (Events Φ)) {X Y : Case.Interface Φ β input}
    (a b : Operand Φ (β.snoc (packedExitType X.exits)) (packedExitType Y.exits)) :
    (handledFunctor (model Φ) policy input).map (X := X) (Y := Y) (Quotient.mk _ a) ≤
        (handledFunctor (model Φ) policy input).map (X := X) (Y := Y) (Quotient.mk _ b) ↔
      (caseRoom Φ).Sat ⟨⟨State, fun _ => True, policy⟩⟩ (captured a b) :=
  (satLe_iff_refines policy a b).symm

/-- On written graphs, the hom order under the semantic functor is
satisfaction of the existing ranked sentence in the model of that policy. -/
theorem ssaHandledFunctor_map_le_iff_sat (input : StructuralContext β) {State : Type}
    (policy : Handler State (Events Φ)) {X Y : Interface Φ β input}
    (p q : CheckedTable Φ (β.snoc (packedExitType X.exits)) Y.exits) :
    (ssaHandledFunctor (model Φ) policy input).map (X := X) (Y := Y) (Quotient.mk _ p) ≤
        (ssaHandledFunctor (model Φ) policy input).map (X := X) (Y := Y) (Quotient.mk _ q) ↔
      (rankedRoom Φ).Sat ⟨⟨State, fun _ => True, policy⟩⟩ (rankedOf p q) := by
  rw [ssaHandledFunctor_map_mk, ssaHandledFunctor_map_mk]
  exact (satLe_iff_refines policy p.toLetCase q.toLetCase).symm.trans
    (Iff.of_eq (congrArg (SatLe _) (grammarCase_read_rankedOf p q).symm))

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
