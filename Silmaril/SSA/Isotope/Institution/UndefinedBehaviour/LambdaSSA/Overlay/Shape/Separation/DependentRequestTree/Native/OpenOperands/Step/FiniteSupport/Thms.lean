module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Entry.State.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Compression
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Runs

/-! # Finite support and compression of guarded refutations -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open CFG.Dependent (Packet)
open CFG.Dependent.Native (withExitUB)
open Syntax (Payload StatePrimitives)
open TwoRequest (Exits)
open ScheduleSearch (StateInventory)

universe u v w

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ}
  {A : Syntax.Ty} {R T : List Syntax.Ty} {σ : Type v}
  {g : Table S R} {h : Table S T} {prim : StatePrimitives Φ σ} {initial : σ}
  {caller : Payload (R.get g.entry)} {p : Packet R} {s : σ}
  {rows : List (RunRow Φ σ)} {stop : RunStop σ}

/-- A finite external observation of the installed native feedback graph
yields the actual typed query derivation. A selected exit is finite in this
graph and receives fresh top when its continuation is applied. -/
theorem FiniteRun.of_feedback_finite {o : Outcome Exits.length Unit σ}
    (finite : Feedback.Finite (g.feedback caller prim) (blockPoint p s) o) :
    ∃ rows stop, FiniteRun g caller prim p s rows stop :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.of_feedback_finite
    finite

theorem FiniteRun.observes (run : FiniteRun g caller prim p s rows stop) :
    g.observeAt caller prim p s = stop.behaviour :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.observes
    run

/-- Agreement on the recorded typed answers suffices to replay a finite
observation, with the terminal store mapped into the new carrier. -/
theorem FiniteRun.replay {τ : Type w} (run : FiniteRun g caller prim p s rows stop)
    (code : σ → τ) (other : StatePrimitives Φ τ)
    (realizes : ∀ r ∈ rows, other r.op r.arg (code r.incoming) = r.answer.mapState code) :
    g.observeAt caller other p (code s) = (stop.mapState code).behaviour :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.replay
    run code other realizes

/-- The start and success/fault answers cover all queried and observed stores. -/
theorem FiniteRun.supported (run : FiniteRun g caller prim p s rows stop)
    (support : RunSupport σ initial) (start : s ∈ support.values)
    (returned : rows.filterMap RunRow.returned? ⊆ support.values) :
    (∀ r ∈ rows, r.incoming ∈ support.values) ∧
      ∀ t, stop.final? = some t → t ∈ support.values :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.covered
    run support start returned

/-- Every row keeps exactly the original typed interpreter answer. -/
theorem FiniteRun.records (run : FiniteRun g caller prim p s rows stop) :
    ∀ r ∈ rows, prim r.op r.arg r.incoming = r.answer :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.records run

variable [DecidableEq σ]

theorem RunSupport.ofRows_bound (initial : σ) (rows : List (RunRow Φ σ)) :
    (RunSupport.ofRows initial rows).values.length ≤ 1 + rows.length :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.ofRows_bound
    initial rows

theorem RunSupport.returned_ofRows (initial : σ) (rows : List (RunRow Φ σ)) :
    rows.filterMap RunRow.returned? ⊆ (RunSupport.ofRows initial rows).values :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.returned_ofRows initial rows

theorem RunSupport.embed_code (support : RunSupport σ initial) {s : σ} (listed : s ∈ support.values) :
    support.embed (support.code s) = s :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.decode_code
    support listed

/-- One finite run's script preserves the observation and all recorded answers. -/
theorem FiniteRun.reconstructs [DecidableEq Φ]
    {caller : Payload (R.get g.entry)} {p : Packet R} {rows : List (RunRow Φ σ)} {stop : RunStop σ}
    (run : FiniteRun g caller prim p initial rows stop) (input : Payload A) :
    let support := RunSupport.ofRows initial rows
    let w := support.witness input rows
    ((g.observeAt caller w.interpreter p w.initial).mapState support.embed = g.observeAt caller prim p initial) ∧
    ∀ row ∈ rows, w.interpreter row.op row.arg (support.code row.incoming) = row.answer.mapState support.code :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.reconstructs
    run input

variable [DecidableEq Φ]
  {raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits}
  {raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits}
  {decodeLeft : Payload A → Payload (R.get g.entry)} {decodeRight : Payload A → Payload (T.get h.entry)}
  {input : Payload A} {rows₀ rows₁ : List (RunRow Φ σ)} {stop₀ stop₁ : RunStop σ}

omit [DecidableEq σ] in
/-- The witnessed caller refutes the pointwise check and hence the shared-entry check. -/
theorem Table.checkers_reject_of_counterexample {n : Nat} (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true)
    (w : EntryCounterexample Φ A n)
    (refutes : ¬ Shape.denote (withExitUB raw g.selected)
        (Syntax.model w.interpreter (g.bindings (decodeLeft w.input))) w.initial ≤
      Shape.denote (withExitUB raw' h.selected)
        (Syntax.model w.interpreter (h.bindings (decodeRight w.input))) w.initial)
    (callers : CallerEnumeration A) (replies : ReplyEnumeration S)
    (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T)
    (stores : StateInventory n) :
    g.checkAllInterpreters? h raw raw' (decodeLeft w.input) (decodeRight w.input) replies left right stores = some false ∧
    ∃ witness, g.compareEntries? h raw raw' callers decodeLeft decodeRight replies left right stores =
      some (.counterexample witness) :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.refuted_checkers
    hg hh w refutes callers replies left right stores

/-- One script on the union of the two finite run supports preserves both
original decorated observations and refutes them at the same caller. The
finite checker consequently rejects on that coded carrier. -/
theorem Table.compress_finite_refutation (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true)
    (lower : FiniteRun g (decodeLeft input) prim ⟨g.entry, decodeLeft input⟩ initial rows₀ stop₀)
    (upper : FiniteRun h (decodeRight input) prim ⟨h.entry, decodeRight input⟩ initial rows₁ stop₁)
    (failed : ¬ Shape.denote (withExitUB raw g.selected)
        (Syntax.model prim (g.bindings (decodeLeft input))) initial ≤
      Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings (decodeRight input))) initial)
    (callers : CallerEnumeration A) (replies : ReplyEnumeration S)
    (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) :
    let support := RunSupport.ofRows initial (rows₀ ++ rows₁)
    let w := support.witness input (rows₀ ++ rows₁)
    support.values.length ≤ 1 + rows₀.length + rows₁.length ∧
    ((Shape.denote (withExitUB raw g.selected)
        (Syntax.model w.interpreter (g.bindings (decodeLeft input))) w.initial).mapState support.embed =
      Shape.denote (withExitUB raw g.selected) (Syntax.model prim (g.bindings (decodeLeft input))) initial) ∧
    ((Shape.denote (withExitUB raw' h.selected)
        (Syntax.model w.interpreter (h.bindings (decodeRight input))) w.initial).mapState support.embed =
      Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings (decodeRight input))) initial) ∧
    (¬ Shape.denote (withExitUB raw g.selected)
        (Syntax.model w.interpreter (g.bindings (decodeLeft input))) w.initial ≤
      Shape.denote (withExitUB raw' h.selected) (Syntax.model w.interpreter (h.bindings (decodeRight input))) w.initial) ∧
    ∀ stores : StateInventory support.values.length,
      g.checkAllInterpreters? h raw raw' (decodeLeft input) (decodeRight input) replies left right stores = some false ∧
      ∃ witness, g.compareEntries? h raw raw' callers decodeLeft decodeRight replies left right stores =
        some (.counterexample witness) :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.compress_refutation
    hg hh lower upper failed callers replies left right

omit [DecidableEq σ] in
/-- Directly from two finite observations of the actual feedback graphs,
extract typed query derivations and a bounded rejecting carrier. Decidable
equality on the original state type is only needed to compute the coding. -/
theorem Table.finite_refutation_hasCarrier
    (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true)
    {o₀ o₁ : Outcome Exits.length Unit σ}
    (lower : Feedback.Finite (g.feedback (decodeLeft input) prim) (blockPoint ⟨g.entry, decodeLeft input⟩ initial) o₀)
    (upper : Feedback.Finite (h.feedback (decodeRight input) prim) (blockPoint ⟨h.entry, decodeRight input⟩ initial) o₁)
    (failed : ¬ Shape.denote (withExitUB raw g.selected)
        (Syntax.model prim (g.bindings (decodeLeft input))) initial ≤
      Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings (decodeRight input))) initial)
    (callers : CallerEnumeration A) (replies : ReplyEnumeration S)
    (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) :
    ∃ (qs₀ qs₁ : List (RunRow Φ σ)) (t₀ t₁ : RunStop σ) (n : Nat),
      FiniteRun g (decodeLeft input) prim ⟨g.entry, decodeLeft input⟩ initial qs₀ t₀ ∧
      FiniteRun h (decodeRight input) prim ⟨h.entry, decodeRight input⟩ initial qs₁ t₁ ∧
      n ≤ 1 + qs₀.length + qs₁.length ∧
      ∀ stores : StateInventory n,
        g.checkAllInterpreters? h raw raw' (decodeLeft input) (decodeRight input) replies left right stores = some false ∧
        ∃ witness, g.compareEntries? h raw raw' callers decodeLeft decodeRight replies left right stores =
          some (.counterexample witness) :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.finite_carrier
    hg hh lower upper failed callers replies left right

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
