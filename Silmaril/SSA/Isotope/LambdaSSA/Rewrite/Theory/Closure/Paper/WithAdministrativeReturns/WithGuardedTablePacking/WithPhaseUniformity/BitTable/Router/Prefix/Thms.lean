module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Router.Prefix.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Router.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.RouterPrefix

/-! # Completeness for router tables without liveness, by request prefixes

No seed is added. Default Paper, `WithGuardedTablePacking` and
`WithPhaseUniformity` are unchanged.

## The model

The request-prefix model is a model of the class that `Valid` quantifies
over: a coherent ordered-trace Kleisli model with the iterator of the
four-reply interpreter and another primitive. So every equation of
`WithPhaseUniformity` holds in it by the general soundness theorem. This
includes the phase-uniformity seed, which is sound in every model of the
class. Nothing is inferred from an interpreter outside that class.
`Router.prefix_sound` is that instance for router tables.

## The observation law

`Router.prefixObservations_unfold`: an observation is the pending first
request, tagged `error` with its label and an empty log, or one completed
exchange followed by what its action allows: nothing after a return, with
the returned Bit tagged `ok`, or an observation of the target. Completed
results and open prefixes carry different tags.

## Completeness without liveness

For any two tables of single labelled requests and any entries these are
equivalent (`Router.labels_eqv_iff`, `Router.labels_eqv_iff_valid'`,
`Router.labels_eqv_iff_prefix`):

* the entered loops are equal in `WithPhaseUniformity`,
* they are valid in every supported model,
* they have the same observations in the request-prefix model,
* some relation that preserves labels and all four actions relates them.

The converse cancels the first exchange as before. Liveness is not needed
because every state has observations: its pending request shows the label
(`Router.prefix_label`), each completed first exchange shows the query
(`Router.prefix_query`), and a jump is told from a return by the pending
request of its target (`Router.prefix_act`).

## The dead loops

`dead_ne`: the two one-state tables whose every reply repeats, with
different labels, are not equal. The distinguishing prefix is the pending
first request (`dead_prefix`, `dead_prefix_not`).

`chain_ne`: two tables of two dead states that differ in the label of
the second state. They have the same complete runs, none
(`chain_observations`). The distinguishing prefix has one completed
exchange (`chain_prefix`, `chain_prefix_not`).

## Not proved

* Rows that are not single labelled requests.
* Nothing is claimed about packed dispatchers in general.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature Trace)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree (Word event)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity

variable {K K' K₁ K₂ : Nat}

/-! ## Soundness -/

/-- Equal entered loops have equal observations in the request-prefix
model. -/
theorem Router.prefix_sound {t : Router K} {t' : Router K'} {i : Fin (K + 1)} {i' : Fin (K' + 1)}
    (e : Eqv false [State] (t.entered i) (t'.entered i') [Bit]) (g : Bool) :
    t.prefixObservations i g = t'.prefixObservations i' g :=
  TableModel.prefix_obs_of_eqv e g

/-- So do loops that are valid in every supported model. -/
theorem Router.prefix_of_valid {t : Router K} {t' : Router K'} {i : Fin (K + 1)} {i' : Fin (K' + 1)}
    (h : Valid (t.entered_typed i).hasType (t'.entered_typed i').hasType) (g : Bool) :
    t.prefixObservations i g = t'.prefixObservations i' g :=
  TableModel.prefix_obs_of_valid h g

section Labels

variable (label₁ : Fin (K₁ + 1) → Bool) (act₁ : Fin (K₁ + 1) → Bool → Bool → Act K₁)
  (label₂ : Fin (K₂ + 1) → Bool) (act₂ : Fin (K₂ + 1) → Bool → Bool → Act K₂)
  (i₁ : Fin (K₁ + 1)) (i₂ : Fin (K₂ + 1))

/-! ## The observation law -/

theorem Router.prefixObservations_unfold (g : Bool) (r : Except Bool (value Bit)) (w : Word) :
    (r, w) ∈ (Router.ofLabels label₁ act₁).prefixObservations i₁ g ↔
      (r = .error (label₁ i₁) ∧ w = 1) ∨
        ∃ tag pl v, w = FreeMonoid.of (event (label₁ i₁) g (tag, pl)) * v ∧
          (Router.ofLabels label₁ act₁).PrefixCont (act₁ i₁ tag pl) r v :=
  TableModel.prefix_unfold label₁ act₁ i₁ g r w

/-- The first request is always observed pending. -/
theorem Router.prefix_pending (g : Bool) :
    (Except.error (label₁ i₁), (1 : Word)) ∈ (Router.ofLabels label₁ act₁).prefixObservations i₁ g :=
  TableModel.prefix_pending label₁ act₁ i₁ g

/-- Equal observations show the same label. -/
theorem Router.prefix_label (g g' : Bool)
    (h : (Router.ofLabels label₁ act₁).prefixObservations i₁ g =
      (Router.ofLabels label₂ act₂).prefixObservations i₂ g') : label₁ i₁ = label₂ i₂ :=
  TableModel.prefix_label label₁ act₁ label₂ act₂ i₁ i₂ g g' h

/-- Equal observations show the same query. -/
theorem Router.prefix_query (g g' : Bool)
    (h : (Router.ofLabels label₁ act₁).prefixObservations i₁ g =
      (Router.ofLabels label₂ act₂).prefixObservations i₂ g') : g = g' :=
  TableModel.prefix_query label₁ act₁ label₂ act₂ i₁ i₂ g g' h

/-- Equal observations give matching actions on every reply. -/
theorem Router.prefix_act (g : Bool) (hl : label₁ i₁ = label₂ i₂)
    (h : (Router.ofLabels label₁ act₁).prefixObservations i₁ g =
      (Router.ofLabels label₂ act₂).prefixObservations i₂ g) (tag pl : Bool) :
    Act.Rel (fun j j' => ∃ q, (Router.ofLabels label₁ act₁).prefixObservations j q =
      (Router.ofLabels label₂ act₂).prefixObservations j' q) (act₁ i₁ tag pl) (act₂ i₂ tag pl) :=
  TableModel.prefix_act_rel label₁ act₁ label₂ act₂ i₁ i₂ g hl h tag pl

/-! ## Completeness without liveness -/

/-- The entered loops are equal exactly when a bisimulation relates the
entries. -/
theorem Router.labels_eqv_iff :
    Eqv false [State] ((Router.ofLabels label₁ act₁).entered i₁) ((Router.ofLabels label₂ act₂).entered i₂)
        [Bit] ↔
      ∃ R : Fin (K₁ + 1) → Fin (K₂ + 1) → Prop, (∀ x y, R x y → label₁ x = label₂ y) ∧
        (∀ x y, R x y → ∀ tag pl, Act.Rel R (act₁ x tag pl) (act₂ y tag pl)) ∧ R i₁ i₂ :=
  ⟨fun e => TableModel.prefix_bisim_of_obs label₁ act₁ label₂ act₂ i₁ i₂ (TableModel.prefix_obs_of_eqv e false),
    fun ⟨R, hl, ha, r⟩ => TableModel.router_eqv_of_bisim label₁ act₁ label₂ act₂ R hl ha i₁ i₂ r⟩

/-- Exactly when their observations in the request-prefix model agree. -/
theorem Router.labels_eqv_iff_prefix :
    Eqv false [State] ((Router.ofLabels label₁ act₁).entered i₁) ((Router.ofLabels label₂ act₂).entered i₂)
        [Bit] ↔
      (Router.ofLabels label₁ act₁).prefixObservations i₁ false =
        (Router.ofLabels label₂ act₂).prefixObservations i₂ false :=
  ⟨fun e => TableModel.prefix_obs_of_eqv e false,
    fun o => (Router.labels_eqv_iff label₁ act₁ label₂ act₂ i₁ i₂).2
      (TableModel.prefix_bisim_of_obs label₁ act₁ label₂ act₂ i₁ i₂ o)⟩

/-- Exactly when they are valid in every supported model. -/
theorem Router.labels_eqv_iff_valid' :
    Eqv false [State] ((Router.ofLabels label₁ act₁).entered i₁) ((Router.ofLabels label₂ act₂).entered i₂)
        [Bit] ↔
      Valid ((Router.ofLabels label₁ act₁).entered_typed i₁).hasType
        ((Router.ofLabels label₂ act₂).entered_typed i₂).hasType :=
  ⟨fun e => valid_of_eqv false e _ _,
    fun v => (Router.labels_eqv_iff_prefix label₁ act₁ label₂ act₂ i₁ i₂).2
      (TableModel.prefix_obs_of_valid v false)⟩

end Labels

/-! ## The dead loops -/

/-- The pending first request of a dead loop. -/
theorem dead_prefix (l g : Bool) :
    (Except.error l, (1 : Word)) ∈ (Router.ofLabels (fun _ => l) deadAct).prefixObservations 0 g :=
  TableModel.prefix_pending (fun _ => l) deadAct 0 g

/-- The dead loop with another label has no such prefix. -/
theorem dead_prefix_not {l l' : Bool} (ne : l ≠ l') (g : Bool) :
    (Except.error l, (1 : Word)) ∉ (Router.ofLabels (fun _ => l') deadAct).prefixObservations 0 g :=
  fun h => ne (Except.error.inj (TableModel.prefix_one (fun _ => l') deadAct 0 g h))

/-- So the two dead loops with different labels are not equal. -/
theorem dead_ne {l l' : Bool} (ne : l ≠ l') :
    ¬ Eqv false [State] ((Router.ofLabels (fun _ => l) deadAct).entered 0)
      ((Router.ofLabels (fun _ => l') deadAct).entered 0) [Bit] :=
  fun e => dead_prefix_not ne false
    ((Set.ext_iff.1 (TableModel.prefix_obs_of_eqv e false) _).1 (dead_prefix l false))

/-- The two chains have the same complete runs: none. -/
theorem chain_observations (a b b' g : Bool) :
    (Router.ofLabels (chainLabel a b) chainAct).observations 0 g =
      (Router.ofLabels (chainLabel a b') chainAct).observations 0 g :=
  (TableModel.router_dead (chainLabel a b) chainAct (fun _ _ pl => ⟨1, pl, rfl⟩) 0 g).trans
    (TableModel.router_dead (chainLabel a b') chainAct (fun _ _ pl => ⟨1, pl, rfl⟩) 0 g).symm

/-- After one completed exchange the second state's request is pending. -/
theorem chain_prefix (a b g : Bool) :
    (Except.error b, FreeMonoid.of (event a g (false, false)) * 1) ∈
      (Router.ofLabels (chainLabel a b) chainAct).prefixObservations 0 g :=
  TableModel.chain_prefix a b g

/-- The chain with another second label has no such prefix. -/
theorem chain_prefix_not (a g : Bool) {b b' : Bool} (ne : b ≠ b') :
    (Except.error b, FreeMonoid.of (event a g (false, false)) * 1) ∉
      (Router.ofLabels (chainLabel a b') chainAct).prefixObservations 0 g :=
  TableModel.chain_prefix_not a g ne

/-- So the two chains are not equal. -/
theorem chain_ne (a : Bool) {b b' : Bool} (ne : b ≠ b') :
    ¬ Eqv false [State] ((Router.ofLabels (chainLabel a b) chainAct).entered 0)
      ((Router.ofLabels (chainLabel a b') chainAct).entered 0) [Bit] :=
  fun e => chain_prefix_not a false ne
    ((Set.ext_iff.1 (TableModel.prefix_obs_of_eqv e false) _).1 (chain_prefix a b false))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
