module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Thms
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.OrderedExits.Thms
import Silmaril.SSA.LambdaRTL.CFG.Thms
meta import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Defs

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Examples

open Silmaril.Elgot (iter liftPure)
open Silmaril.Elgot.ITree (Tree Trace HasTrace HandledTrace vis vis_bind
  iterate_fixpoint iterate_forever iterate_uniformity diverge diverge_bind out_injective out_vis out_ret out_diverge)
open Silmaril.Elgot.ITree.Finite (Event evaluate headFrom out_evaluate)
open Silmaril.Logic.ITree.TraceInstitution (Sat)
open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph br)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.OrderedExits (Pending execute step run)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible (Atom Denote
  PacketType PrimitiveSignature)
open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction (Transfer)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues typeModel)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open NamedFlat.Entry.Reverse (Lowered Registers lowerCheckedWith numberedInterface)
open NamedFlat.Entry.Record (Input)

private abbrev Reg := ULift.{1} Nat
private abbrev SortName := ULift.{1} Unit
private instance : AtomValues SortName := ⟨fun _ => PUnit⟩
private abbrev Runtime := Sigma (AtomValues.carrier (κ := SortName))

private def signature : PrimitiveSignature Unit := ⟨fun _ => .unit, fun _ => .unit⟩
private abbrev Events := Event signature.Request signature.Reply
private def key : signature.Request := ⟨(), ⟨⟩⟩

private instance : HasTy Unit PacketType := signature.typing
private instance : HasTy Unit (Ty SortName) := ⟨fun _ => .unit, fun _ => .unit⟩
private instance : HasEff Unit Bool := ⟨fun _ => true⟩
private abbrev sig : FlatInstitution.Signature.{0, 0} SortName where
  Instr := Unit

attribute [local instance] typeModel

private def model : LambdaSSA.Semantics.Interaction.Typed.Ordered.Model (κ := SortName) Events sig.Instr where
  raw _ _ := vis (.ask key) (fun _ => pure .unit)
  instructions := {
    denote := fun _ _ => vis (.ask key) (fun _ => pure PUnit.unit)
    denotePure := fun _ h _ => by contradiction
    denote_pure := fun _ h _ => by contradiction }
  compatible _ input := by
    cases input
    change vis (.ask key) (fun _ => pure Value.unit) =
      ((vis (.ask key) (fun _ => pure PUnit.unit) : Tree Events PUnit.{2}) >>= fun _ => pure Value.unit)
    rw [vis_bind]
    simp only [pure_bind]

private def entryReg : Reg := ⟨0⟩
private def replyReg : Reg := ⟨1⟩
private def carried : Reg := ⟨2⟩
private def header : Reg := ⟨8⟩
private def exits : List (Option Reg) := [some ⟨40⟩, none]

-- The loop carries the reply through a genuine self-edge φ row. The other
-- graph terminates at exit 1 with the same payload type as exit 0.
private def graph (returns : Bool) : Graph Reg Reg Unit :=
  ⟨.let1 replyReg (.app () (.var entryReg)) (.term (br header)),
    [(header, ⟨[⟨carried, (none, .var replyReg) ::
        (if returns then [] else [(some header, .var carried)])⟩],
      .term (if returns then .br none (.pair (.var carried) .unit) else br header)⟩)]⟩

private def context : BoundCtx (Ty SortName) 1 := .snoc .nil .unit
private def ports := numberedInterface context exits (fun _ => .unit)
private def captures : Captures Reg context where
  names _ := some entryReg
  distinct i j _ := Subsingleton.elim i j
  privateUnit _ eq := by nomatch eq

private def fields (_ : Option Reg) : List (Reg × Ty SortName) := []
private def admission (returns : Bool) : Admission sig ports fields captures :=
  (admit ports fields captures (graph returns) [entryReg] [(header, [])]
    (fun _ => .product (.product .unit .unit) (.product .unit .unit))).get
      (by cases returns <;> decide)

private def registers : Registers Reg := ⟨⟨1⟩, fun i => ⟨i + 2⟩⟩
private def lowered (returns : Bool) : Lowered ports fields (admission returns).code :=
  (lowerCheckedWith ports fields registers (fun _ => registers.localAt)
    (fun _ => some header) (admission returns).code).get (by cases returns <;> decide)

private def recompiled (returns : Bool) :
    NamedFlat.Entry.LiveOut.Admission sig ports fields (lowered returns).source :=
  (NamedFlat.Entry.LiveOut.admit (P := sig) ports fields (lowered returns).source
    (fun _ => .product (.product (.product .unit .unit) (.product .unit .unit))
      (.product .unit .unit))).get (by cases returns <;> decide)

example : ((lowered false).source.blocks.lookup (some header)).any
    (fun block => block.body.targets.contains (some header)) := by decide

private def inputTypes : Fin 1 → PacketType := fun _ => .unit
private def outputTypes : Fin 2 → PacketType := fun _ => .product .unit .unit
private def localTypes : Fin 2 → PacketType := fun _ => .unit

private def program (returns : Bool) : Visible.Program signature inputTypes outputTypes where
  locals := 2
  localType := localTypes
  entry _ := .inl 0
  entryType _ := rfl
  block := Fin.cases (.apply () (.var .here) (.inl 1) (.var .here))
    (fun _ => .term (if returns then .jump (.inr 1) (.pair (.var .here) .unit)
      else .jump (.inl 1) (.var .here)))

private def packet : Denote (inputTypes 0) := ⟨⟩
private def publicCaptures : Fin 1 → Reg := fun _ => entryReg
private def publicContext : BoundCtx PacketType 1 := .snoc .nil .unit

private def packed (returns : Bool) : Visible.Program.PackedEntry (program returns) 0 where
  count := 1
  captures := publicCaptures
  context := publicContext
  blocks := localTypes
  exits := outputTypes
  target := (NamedFlat.elaborate ((program returns).compile 0) (program returns).exits publicCaptures).get
    (by cases returns <;> decide)
  accepted := Option.some_get _ |>.symm
  typed := NamedFlat.check_sound _ _ _ _ (by cases returns <;> decide)

private def publicEnv : Env Atom := fun _ => .unit
private def record : Input context := (PUnit.unit, PUnit.unit)
private def ambient : Env Runtime := fun _ => .unit

private def encodePayload : Value Runtime → Value Atom
  | .atom _ => .atom ⟨⟩
  | .unit => .unit
  | .pair x y => .pair (encodePayload x) (encodePayload y)
  | .inl x => .inl (encodePayload x)
  | .inr x => .inr (encodePayload x)

private def observeResult (out : Transfer Runtime) : Transfer Atom := (out.1, encodePayload out.2)

private def result : Transfer Atom := FiniteCFG.packedTreeOutput (1, .pair .unit .unit)

private noncomputable def behavior (returns : Bool) : Tree Events (Transfer Atom) :=
  vis (.ask key) fun _ => if returns then pure result else diverge

private theorem fixed_loop {A B : Type 1} (step : A → Tree Events (B ⊕ A)) (state : A)
    (fixed : step state = pure (.inr state)) : iter step state = diverge := by
  let loop (_ : PUnit.{2}) : Tree Events (B ⊕ PUnit.{2}) := pure (.inr PUnit.unit)
  have same := iterate_uniformity loop step (fun _ => state) (by
    funext x
    cases x
    change ((pure (Sum.inr PUnit.unit) : Tree Events (B ⊕ PUnit.{2})) >>= _) = (pure state >>= _)
    simp only [pure_bind]
    exact fixed.symm)
  have evaluated := congrFun same PUnit.unit
  change iter loop PUnit.unit = (pure state >>= iter step) at evaluated
  rw [pure_bind] at evaluated
  exact evaluated.symm.trans (iterate_forever PUnit.unit)

private def σ := captures.store record
private def initial : Pending Reg Reg (Value Runtime) :=
  (none, some header, .unit, upd σ replyReg .unit)
private def next (returns : Bool) : Pending Reg Reg (Value Runtime) :=
  (some header, if returns then none else some header,
    if returns then .pair .unit .unit else .unit, upd initial.2.2.2 carried .unit)
private def machine := NamedFlat.treeModel model.raw
private noncomputable def sourceStep (returns : Bool) := step machine (graph returns)

private theorem source_entry (returns : Bool) :
    execute machine none (graph returns).entry σ = vis (.ask key) (fun _ => pure initial) := by
  simp only [graph, execute, CFG.Body.exec, Op.eval, machine, NamedFlat.treeModel, model,
    vis_bind, CFG.Term.exec, br, pure_bind]
  rfl

private theorem source_first (returns : Bool) : sourceStep returns initial = pure (.inr (next returns)) := by
  cases returns
  · change Sum.inr <$> (pure (next false) : Tree Events (Pending Reg Reg (Value Runtime))) =
      (pure (.inr (next false)) : Tree Events ((Option Reg × Value Runtime) ⊕ Pending Reg Reg (Value Runtime)))
    rw [map_pure]
  · change Sum.inr <$> (pure (next true) : Tree Events (Pending Reg Reg (Value Runtime))) =
      (pure (.inr (next true)) : Tree Events ((Option Reg × Value Runtime) ⊕ Pending Reg Reg (Value Runtime)))
    rw [map_pure]

private theorem source_fixed : sourceStep false (next false) = pure (.inr (next false)) := by
  change Sum.inr <$> (pure (some header, some header, .unit, upd (next false).2.2.2 carried .unit) :
    Tree Events (Pending Reg Reg (Value Runtime))) = _
  have store_eq : upd (next false).2.2.2 carried .unit = (next false).2.2.2 := by
    funext name
    by_cases hit : name = carried <;> simp [next, upd, hit]
  rw [map_pure, store_eq]
  rfl

private theorem source_observation (returns : Bool) :
    observeResult <$> (admission returns).observe model record = behavior returns := by
  have graph_eq : (admission returns).source = graph returns := by cases returns <;> rfl
  have leave : sourceStep true (next true) = pure (.inl (none, .pair .unit .unit)) := rfl
  unfold Admission.observe
  rw [graph_eq]
  change observeResult <$> ((execute machine none (graph returns).entry σ >>= iter (sourceStep returns)) >>= _) = _
  rw [source_entry]
  simp only [map_eq_pure_bind, vis_bind, pure_bind]
  rw [congrFun (iterate_fixpoint (sourceStep returns)) initial, source_first, pure_bind, Sum.elim_inr]
  cases returns
  · rw [fixed_loop _ _ source_fixed]
    simp only [behavior, diverge_bind]
    rfl
  · rw [congrFun (iterate_fixpoint (sourceStep true)) (next true), leave, pure_bind, Sum.elim_inl]
    simp only [pure_bind]
    rfl

private def afterRequest (returns : Bool) (_ : signature.Reply key) : (program returns).State := by
  change ULift (Visible.PacketAt (Sum.elim localTypes outputTypes))
  exact ⟨⟨.inl 1, ⟨⟩⟩⟩

private theorem public_first (returns : Bool) :
    evaluate (program returns).step ((program returns).start 0 packet) =
      vis (.ask key) (evaluate (program returns).step ∘ afterRequest returns) := by
  apply out_injective
  rw [out_evaluate _ _ (program returns).mem_states, out_vis]
  cases returns <;> cbv

private theorem public_spin (reply : signature.Reply key) :
    evaluate (program false).step (afterRequest false reply) = diverge := by
  apply out_injective
  rw [out_evaluate _ _ (program false).mem_states, out_diverge]
  cases reply
  cbv

private def returned : Visible.Program.Result outputTypes := ⟨⟨1, (⟨⟩, ⟨⟩)⟩⟩

private theorem public_return (reply : signature.Reply key) :
    evaluate (program true).step (afterRequest true reply) = pure returned := by
  change _ = Silmaril.Elgot.ITree.ret returned
  apply out_injective
  rw [out_evaluate _ _ (program true).mem_states, out_ret]
  cases reply
  cbv

private theorem public_agrees (returns : Bool) : (packed returns).recordAgrees packet publicEnv :=
  fun _ => rfl

private theorem public_observation (returns : Bool) :
    (packed returns).observe publicEnv publicEnv = behavior returns := by
  rw [(packed returns).observe_eq packet _ _ (public_agrees returns), (program returns).observe_eq,
    public_first, vis_bind, vis_bind]
  unfold behavior
  congr 1
  funext reply
  cases returns
  · simp only [Function.comp_apply, public_spin, diverge_bind]
    rfl
  · simp only [Function.comp_apply, public_return, pure_bind]
    rfl

private noncomputable def alignment (returns : Bool) :
    PublicMatch (admission returns) model record packet observeResult
      (packed returns) publicEnv publicEnv ambient where
  lowered := lowered returns
  recompiled := recompiled returns
  agrees := public_agrees returns
  observes :=
    (congrArg (Functor.map observeResult)
      ((admission returns).observe_roundTrip (lowered returns) (recompiled returns) model record ambient)).symm.trans
      ((source_observation returns).trans (public_observation returns).symm)

/-- Losing an ordered return is permitted by directed trace inclusion. -/
theorem looping_refines_returning (policy : Silmaril.Logic.ITree.Model.{0, 0} signature.traceSignature.toSignature) :
    Sat policy ⟨_, observeResult <$> (admission false).observe model record,
      HasTrace (observeResult <$> (admission true).observe model record)⟩ :=
  (refinementAt?_iff_source (alignment false) (alignment true)).mp (by cbv) policy

/-- The reverse orientation fails over the model class at the same packet. -/
theorem returning_does_not_refine_looping :
    ¬ ∀ policy : Silmaril.Logic.ITree.Model.{0, 0} signature.traceSignature.toSignature,
      Sat policy ⟨_, observeResult <$> (admission true).observe model record,
        HasTrace (observeResult <$> (admission false).observe model record)⟩ := by
  intro valid
  have verdict := (refinementAt?_iff_source (alignment true) (alignment false)).mpr valid
  have rejected : (program true).refinementAt? (program false) 0 packet = false := by cbv
  rw [rejected] at verdict
  cases verdict

private def handler := signature.traceModelWithHandler
  (fun (seen : Bool) _ _ => if seen then none else some true) (fun seen => !seen)

private def returnTrace : Visible.Program.ObservationTrace signature :=
  .exchange (.ask key) PUnit.unit (.result result)

private theorem handled_return :
    HandledTrace handler.step false (observeResult <$> (admission true).observe model record) returnTrace := by
  change HasTrace (observeResult <$> (admission true).observe model record) returnTrace ∧ _
  refine ⟨?_, ⟨true, rfl, trivial⟩⟩
  rw [source_observation]
  exact (Silmaril.Elgot.ITree.hasTrace_vis_exchange_iff _ _ _ _).mpr (out_ret _)

example : HandledTrace handler.step false
    (observeResult <$> NamedFlat.Entry.Reverse.observeAttached model ports fields (lowered true).source record)
    returnTrace :=
  ((alignment true).handledTrace_iff handler false returnTrace).mp handled_return

example (policy : Silmaril.Logic.ITree.Model.{0, 0} signature.traceSignature.toSignature) :
    Sat policy ⟨_, observeResult <$> NamedFlat.Entry.Reverse.observeAttached model ports fields (lowered false).source record,
      HasTrace (observeResult <$> NamedFlat.Entry.Reverse.observeAttached model ports fields (lowered true).source record)⟩ :=
  ((alignment false).sat_rtl_iff (alignment true) policy).mp (looping_refines_returning policy)

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Examples
