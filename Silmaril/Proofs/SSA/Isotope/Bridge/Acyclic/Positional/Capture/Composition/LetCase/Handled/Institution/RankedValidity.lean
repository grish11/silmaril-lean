module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Defs
import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Categorical.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Categorical.Realization.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Soundness.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Kleisli.Thms

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.Institution (InstrSig)
open Silmaril.Isotope.Institution.Acyclic (CaseEquation CoherentRegionModel compileFiniteExit)
open Silmaril.Isotope.Institution.Acyclic.Captured (RankedEntry RankedEquation denoteRanked grammarCase readGrammar
  readGrammar_finiteExit)
open Region (packedExitType)
open LambdaSSA.Semantics.Categorical (denoteRegion labelInject singletonLabelPayload packLabelExit unpackLabelExit
  unpackLabelExit_packLabelExit)
open LambdaSSA.Semantics.Categorical.SingletonDispatcher (labelInject_payload)
open LetIter.Semantics.Categorical (denote_equiv_of_coherent_shared_tensor typingCoherent_ofType)
open LetCase.LocallyNameless (Equiv)
open LetCase.Structural.Finite (Context StructuralContext equiv_iff_traceArrow_eq equiv_iff_traceArrow_eq_snoc)
open LetCase.Structural.Reply (Γ₀ traceArrow traceArrow_of_valid valid_of_equiv)
open LetSeq.StraightLine.Structural.Categorical (traceJ traceTypes traceInstructions)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

section General

variable {τ ε : Type} [TypeFormers τ] {P : InstrSig τ ε}

/-- The existing emission of a ranked sentence is the pair of operands
emitted from its two entries, at the packed result type. -/
theorem emitted_case_proof (e : RankedEquation P) :
    grammarCase (readGrammar e) =
      ⟨⟨e.1.depth, e.1.bound, packedExitType e.1.exits⟩, emitted e.2.1, emitted e.2.2⟩ :=
  (congrArg compileFiniteExit (readGrammar_finiteExit e)).trans rfl

variable {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (K : CoherentRegionModel J P)
  {d : Nat} {β : BoundCtx τ d} {L : List τ}

/-- In every model of the ranked room, the ordered-exit arrows of two
entries agree exactly when the arrows of their emitted operands agree. -/
theorem denoteRanked_eq_iff_proof (l r : RankedEntry P.Instr β L) :
    denoteRanked J K l = denoteRanked J K r ↔
      (letI := K.instructions
       LetCase.Semantics.Categorical.denote J K.types (emitted l).2 =
         LetCase.Semantics.Categorical.denote J K.types (emitted r).2) := by
  let := K.instructions
  have := K.coherent
  have left := Table.toLetCase_denote J K.types l.table l.checked l.index l.entry
  have right := Table.toLetCase_denote J K.types r.table r.checked r.index r.entry
  change denoteRegion J K.types (l.table.toSSA_hasType l.index l.entry) =
    denoteRegion J K.types (r.table.toSSA_hasType r.index r.entry) ↔
    LetCase.Semantics.Categorical.denote J K.types (l.table.toLetCase l.checked l.index l.entry).2 =
      LetCase.Semantics.Categorical.denote J K.types (r.table.toLetCase r.checked r.index r.entry).2
  rw [left, right]
  have := contextMap_isIso K.types β
  constructor
  · intro same
    have out := congrArg (fun f => f ≫ J.map (packLabelExit K.types L ≫
      singletonLabelPayload K.types (packedExitType L))) same
    simp only [Category.assoc, ← Functor.map_comp] at out
    have cancel : labelInject K.types (L := [packedExitType L]) 0 rfl ≫ unpackLabelExit K.types L ≫
        packLabelExit K.types L ≫ singletonLabelPayload K.types (packedExitType L) = 𝟙 _ := by
      rw [← Category.assoc (unpackLabelExit K.types L), unpackLabelExit_packLabelExit,
        Category.id_comp, labelInject_payload]
    rw [cancel, J.map_id, Category.comp_id, Category.comp_id] at out
    exact (cancel_epi (J.map (contextMap K.types β))).mp out
  · intro same
    rw [same]

/-- Native equations between emitted operands hold in every supported
model of the ranked room. -/
theorem sat_of_derivable_proof {pe : ε} (supported : Supported pe K) (l r : RankedEntry P.Instr β L)
    (h : Equiv pe (Ctx.nil : Ctx Empty τ) β (emitted l).1 (emitted r).1 (packedExitType L)) :
    denoteRanked J K l = denoteRanked J K r := by
  refine (denoteRanked_eq_iff_proof K l r).mpr ?_
  let := K.instructions
  rw [← Native.denote_caseIter J K.types, ← Native.denote_caseIter J K.types]
  exact denote_equiv_of_coherent_shared_tensor J K.types supported.typing supported.shared supported.pure
    (Morphism.CaseIter.embed_equiv h) _ _

end General

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ]

theorem separated_of_structural_proof {n : Nat} {γ : Context n} (input : StructuralContext γ) :
    Separated (Φ := Φ) γ :=
  fun d e same => (equiv_iff_traceArrow_eq input d e).mpr same

theorem separated_snoc_proof {n : Nat} {β : Context n} (input : StructuralContext β) (X : Ty Empty) :
    Separated (Φ := Φ) (β.snoc X) :=
  fun d e same => (equiv_iff_traceArrow_eq_snoc input d e).mpr same

/-- The ordered trace model is a supported model of the ranked room. -/
theorem trace_supported_proof : Supported false (traceRegionModel Φ) := by
  classical
  exact ⟨typingCoherent_ofType (ν := Empty) (fun _ : Empty => Nat) LetSeq.StraightLine.Structural.model,
    fun _ _ => ⟨rfl, rfl⟩, fun _ pure => by cases pure⟩

set_option backward.isDefEq.respectTransparency false in
/-- At the ordered trace model, two entries with equal ordered-exit arrows
have natively equal emitted operands, over a separated bound context. -/
theorem derivable_of_trace_proof {d : Nat} {β : Context d} {L : List (Ty Empty)} (separated : Separated (Φ := Φ) β)
    (l r : RankedEntry Φ β L)
    (same : denoteRanked (traceJ (α := Empty) (Φ := Φ)) (traceRegionModel Φ) l =
      denoteRanked (traceJ (α := Empty) (Φ := Φ)) (traceRegionModel Φ) r) :
    Equiv false Γ₀ β (emitted (P := sig Φ) l).1 (emitted (P := sig Φ) r).1 (packedExitType L) := by
  have arrows := (denoteRanked_eq_iff_proof (traceRegionModel Φ) l r).mp same
  let := traceInstructions (α := Empty) (Φ := Φ)
  refine separated (emitted (P := sig Φ) l).2 (emitted (P := sig Φ) r).2 ?_
  unfold traceArrow LetIter.Semantics.Categorical.denoteOfType
  rw [Native.denote_caseIter (traceJ (α := Empty) (Φ := Φ)) (traceTypes Empty),
    Native.denote_caseIter (traceJ (α := Empty) (Φ := Φ)) (traceTypes Empty)]
  exact arrows

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
