module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Renaming.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.RankedValidity

/-! # Soundness and completeness in the existing categorical ranked room

In every model of the existing ranked room, two ranked entries have the
same ordered-exit arrow exactly when their emitted LetCase operands have
the same arrow. This uses only the checked emitter factorization.

Native LetCase equations between the emitted operands are sound in the
supported models: those with coherent expression typing, a shared tensor
and pure interpretations of pure primitives. Membership in the room gives
coherence of region witnesses only, so soundness is stated for the
supported models and not for every model of the room.

For the finite structural signature the ordered trace model is supported.
Over a separated bound context it reflects native equality. A ranked
sentence is therefore valid in all supported models exactly when its
emitted operands are natively equal.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.ITree.TraceInstitution (allRepliesModel)
open Silmaril.Isotope.Institution (InstrSig)
open Silmaril.Isotope.Institution.Acyclic (CaseEquation CoherentRegionModel)
open Silmaril.Isotope.Institution.Acyclic.Captured (RankedEntry RankedEquation denoteRanked grammarCase readGrammar)
open Region (packedExitType)
open Reverse (CheckedTable)
open LetCase.LocallyNameless (Equiv)
open LetCase.Structural.Finite (Context StructuralContext)
open LetCase.Structural.Reply (Γ₀)
open LetSeq.StraightLine.Structural.Categorical (traceJ)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

/-! ## Every model of the room -/

section General

variable {τ ε : Type} [TypeFormers τ] {P : InstrSig τ ε}

/-- The existing emission of a ranked sentence is the pair of operands
emitted from its two entries. -/
theorem emitted_case (e : RankedEquation P) :
    grammarCase (readGrammar e) =
      ⟨⟨e.1.depth, e.1.bound, packedExitType e.1.exits⟩, emitted e.2.1, emitted e.2.2⟩ :=
  emitted_case_proof e

/-- Native equality of the emitted sentence, on the emitted operands. -/
theorem derivable_iff (pe : ε) (e : RankedEquation P) :
    Derivable pe (grammarCase (readGrammar e)) ↔
      Equiv pe (Ctx.nil : Ctx Empty τ) e.1.bound (emitted e.2.1).1 (emitted e.2.2).1
        (packedExitType e.1.exits) := by
  rw [emitted_case]
  exact Iff.rfl

variable {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (K : CoherentRegionModel J P)

/-- Satisfaction in the existing ranked room is equality of the original
ordered-exit arrows of the two entries. -/
theorem sat_iff_denoteRanked (e : RankedEquation P) :
    (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom J P).Sat
        (ShrinkHoms.toShrinkHoms (Discrete.mk K)) e ↔
      denoteRanked J K e.2.1 = denoteRanked J K e.2.2 :=
  Iff.rfl

/-- In every model of the room, the ordered-exit arrows of two entries
agree exactly when the arrows of their emitted operands agree. -/
theorem denoteRanked_eq_iff {d : Nat} {β : BoundCtx τ d} {L : List τ} (l r : RankedEntry P.Instr β L) :
    denoteRanked J K l = denoteRanked J K r ↔
      (letI := K.instructions
       LetCase.Semantics.Categorical.denote J K.types (emitted l).2 =
         LetCase.Semantics.Categorical.denote J K.types (emitted r).2) :=
  denoteRanked_eq_iff_proof K l r

/-- The existing signature reduct: a ranked sentence that holds in every
model of the room over the source signature has a translation that holds
in every model over the target signature, for the same functor. This is
for all models of the room. -/
theorem sat_mapRanked_of_all {υ δ : Type} [TypeFormers υ] {Q : InstrSig υ δ}
    (g : Morphism.SignatureMap P.Instr Q.Instr τ υ ε δ) [g.PreservesProducts] [g.PreservesSums]
    (e : RankedEquation P)
    (all : ∀ N : (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom J P).Mod,
      (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom J P).Sat N e)
    (N : (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom J Q).Mod) :
    (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom J Q).Sat N
      (Silmaril.Isotope.Institution.Acyclic.Captured.mapRanked g e) :=
  (Silmaril.Isotope.Institution.Acyclic.Captured.sat_mapRanked g N e).mpr (all _)

/-! ## Soundness in supported models -/

variable {pe : ε}

/-- A natively derivable ranked sentence holds in every supported model. -/
theorem sat_of_derivable (supported : Supported pe K) (e : RankedEquation P)
    (h : Derivable pe (grammarCase (readGrammar e))) :
    (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom J P).Sat
      (ShrinkHoms.toShrinkHoms (Discrete.mk K)) e :=
  sat_of_derivable_proof K supported e.2.1 e.2.2 ((derivable_iff pe e).mp h)

end General

theorem rankedValid_of_derivable {τ ε : Type} [TypeFormers τ] {P : InstrSig τ ε} {pe : ε}
    (e : RankedEquation P) (h : Derivable pe (grammarCase (readGrammar e))) : RankedValid pe e := by
  intro V C vcat ccat cart sym prem symPrem sumV sumC distV distC iter elgot J freyd central K supported
  exact sat_of_derivable K supported e h

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ]

/-! ## Reflection at the ordered trace model -/

/-- A structural bound context is separated. -/
theorem separated_of_structural {n : Nat} {γ : Context n} (input : StructuralContext γ) :
    Separated (Φ := Φ) γ :=
  separated_of_structural_proof input

/-- A structural older context below any input type is separated. The
input may be a literal packed type with its empty tail. -/
theorem separated_snoc {n : Nat} {β : Context n} (input : StructuralContext β) (X : Ty Empty) :
    Separated (Φ := Φ) (β.snoc X) :=
  separated_snoc_proof input X

/-- The ordered trace model is a supported model of the ranked room. -/
theorem trace_supported : Supported false (traceRegionModel Φ) :=
  trace_supported_proof

/-- A ranked sentence that holds at the ordered trace model, over a
separated bound context, is natively derivable. -/
theorem derivable_of_trace (e : RankedEquation (sig Φ))
    (separated : Separated (Φ := Φ) (grammarCase (readGrammar e)).1.bound)
    (holds : (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Empty) (Φ := Φ)) (sig Φ)).Sat
      (traceRankedModel Φ) e) :
    Derivable false (grammarCase (readGrammar e)) := by
  rw [emitted_case] at separated
  exact (derivable_iff false e).mpr (derivable_of_trace_proof separated e.2.1 e.2.2 holds)

/-! ## Soundness and completeness -/

/-- A ranked sentence over a separated bound context holds in every
supported model of the existing ranked room exactly when its emitted
operands are natively equal. -/
theorem rankedValid_iff (e : RankedEquation (sig Φ))
    (separated : Separated (Φ := Φ) (grammarCase (readGrammar e)).1.bound) :
    RankedValid false e ↔ Derivable false (grammarCase (readGrammar e)) :=
  ⟨fun valid => derivable_of_trace e separated (valid (traceJ (α := Empty) (Φ := Φ)) (traceRegionModel Φ)
      trace_supported),
    rankedValid_of_derivable e⟩

/-- Validity is decided by the one ordered trace model. -/
theorem rankedValid_iff_trace (e : RankedEquation (sig Φ))
    (separated : Separated (Φ := Φ) (grammarCase (readGrammar e)).1.bound) :
    RankedValid false e ↔
      (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Empty) (Φ := Φ)) (sig Φ)).Sat
        (traceRankedModel Φ) e :=
  ⟨fun valid => valid (traceJ (α := Empty) (Φ := Φ)) (traceRegionModel Φ) trace_supported,
    fun holds => rankedValid_of_derivable e (derivable_of_trace e separated holds)⟩

variable {d : Nat} {β : Context d} {A B : Ty Empty} {I J : LCtx (Ty Empty)}

/-- On written graphs with a structural older context below the literal
packed input, validity is native equality of the emitted operands. -/
theorem rankedValid_rankedOf_iff (input : StructuralContext β)
    (p q : CheckedTable Φ (β.snoc (packedExitType I)) J) :
    RankedValid false (rankedOf p q) ↔
      Equiv false Γ₀ (β.snoc (packedExitType I)) p.toLetCase.1 q.toLetCase.1 (packedExitType J) :=
  (rankedValid_iff (rankedOf p q) (by rw [grammarCase_read_rankedOf]; exact separated_snoc input _)).trans
    (by rw [grammarCase_read_rankedOf]; exact Iff.rfl)

/-- Validity in the categorical ranked room is validity in all
handled-trace models, on written graphs. -/
theorem rankedValid_iff_handled_valid (input : StructuralContext β)
    (p q : CheckedTable Φ (β.snoc (packedExitType I)) J) :
    RankedValid false (rankedOf p q) ↔
      ∀ M : HandledModel Φ, (rankedRoom Φ).Sat ⟨M⟩ (rankedOf p q) :=
  (rankedValid_rankedOf_iff input p q).trans ((valid_iff_equiv input p.toLetCase q.toLetCase).symm.trans
    (forall_congr' fun M => Iff.of_eq (congrArg (SatLe M) (grammarCase_read_rankedOf p q).symm)))

/-! ## Injective renamings -/

variable {Ψ₀ Ψ : Type} [LetCase.Structural.Finite.Signature Ψ] {r : Ψ₀ → Ψ}

/-- Native equality of captured operands is preserved and reflected by an
injective renaming that keeps the typed interface. -/
theorem equiv_rename_iff (input : StructuralContext β) (injective : Function.Injective r)
    (a b : Operand (Pulled r) (β.snoc A) B) :
    Equiv false Γ₀ (β.snoc A) (renameOperand r a).1 (renameOperand r b).1 B ↔
      Equiv false Γ₀ (β.snoc A) a.1 b.1 B := by
  refine (satLe_iff_equiv input allReplies_exposing (renameOperand r a) (renameOperand r b)).symm.trans ?_
  refine (satLe_rename injective (allRepliesModel (events Ψ)) (captured a b)).trans ?_
  rw [reduct_allReplies]
  exact satLe_iff_equiv input allReplies_exposing a b

/-- Validity of a ranked sentence on written graphs is preserved and
reflected by an injective renaming, using the existing ranked signature map. -/
theorem rankedValid_rename_iff (input : StructuralContext β) (injective : Function.Injective r)
    (p q : CheckedTable (Pulled r) (β.snoc (packedExitType I)) J) :
    RankedValid false (renameRanked r (rankedOf p q)) ↔ RankedValid false (rankedOf p q) := by
  have emittedCase : grammarCase (readGrammar (renameRanked r (rankedOf p q))) =
      captured (renameOperand r p.toLetCase) (renameOperand r q.toLetCase) := by
    rw [readGrammar_renameRanked, grammarCase_renameGrammar, grammarCase_read_rankedOf]
    rfl
  refine (rankedValid_iff _ (by rw [emittedCase]; exact separated_snoc input _)).trans ?_
  rw [emittedCase]
  exact (equiv_rename_iff input injective p.toLetCase q.toLetCase).trans
    (rankedValid_rankedOf_iff input p q).symm

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
