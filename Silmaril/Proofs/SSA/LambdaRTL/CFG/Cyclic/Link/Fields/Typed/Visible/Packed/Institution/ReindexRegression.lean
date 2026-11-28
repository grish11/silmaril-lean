module

import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Reindex.Thms
import Silmaril.Semantics.ITree.Signature.Execution.Thms
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Lift.Composition.Thms
import Mathlib.Tactic.FinCases
meta import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Defs

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

open CategoryTheory
open Silmaril.Elgot.ITree
open Silmaril.Elgot.ITree.Finite (Event evaluate headFrom out_evaluate)
open Silmaril.Isotope (BoundCtx Value)
open Silmaril.Isotope.Bridge.NamedFlat (elaborate check_sound)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Logic.ITree

private abbrev bit : PacketType := .coprod .unit .unit
private abbrev signature : PrimitiveSignature Bool := ⟨fun _ => .unit, fun _ => bit⟩
private def inputs : Fin 1 → PacketType := fun _ => .unit
private def outputs : Fin 2 → PacketType := fun _ => .unit
private def locals : Fin 2 → PacketType := Fin.cases .unit (fun _ => bit)

-- A request uses the selected opcode. The first reply returns to port zero,
-- and the second reply can return to a different ordered port.
private def fixture (opcode : Bool) (second : Fin 2) : Program signature inputs outputs where
  locals := 2
  localType := locals
  entry _ := .inl 0
  entryType _ := rfl
  block i := Fin.cases (.apply opcode .unit (.inl 1) (.var .here))
    (fun _ => .term (.case (.var .here) (.jump (.inr 0) .unit) (.jump (.inr second) .unit))) i

private def packet : Denote (inputs 0) := ⟨⟩
private abbrev key (opcode : Bool) : signature.Request := ⟨opcode, ⟨⟩⟩
private def captures : Fin 1 → Register := fun _ => ⟨0⟩
private def context : BoundCtx PacketType 1 := .snoc .nil .unit
private instance : Silmaril.HasTy Bool PacketType := signature.typing
private def env : Semantics.Env Atom := fun _ => .unit

private theorem admits (opcode : Bool) (second : Fin 2) :
    (elaborate ((fixture opcode second).compile 0) (fixture opcode second).exits captures).isSome := by
  cases opcode <;> fin_cases second <;> decide

private def target (opcode : Bool) (second : Fin 2) :=
  (elaborate ((fixture opcode second).compile 0) (fixture opcode second).exits captures).get (admits opcode second)

private def packed (opcode : Bool) (second : Fin 2) : Program.PackedEntry (fixture opcode second) 0 where
  count := 1
  captures := captures
  context := context
  blocks := locals
  exits := outputs
  target := target opcode second
  accepted := Option.eq_some_of_isSome (admits opcode second)
  typed := check_sound _ _ _ _ (by cases opcode <;> fin_cases second <;> decide)

private def port (second : Fin 2) : Denote bit → Fin 2
  | .inl _ => 0
  | .inr _ => second

private def afterReply (opcode : Bool) (second : Fin 2) (reply : signature.Reply (key opcode)) :
    (fixture opcode second).State := by
  change ULift (PacketAt (Sum.elim locals outputs))
  exact ⟨⟨.inl 1, reply⟩⟩

private theorem packed_shape (opcode : Bool) (second : Fin 2) :
    (packed opcode second).observe env env =
      vis (.ask (key opcode)) (fun (reply : signature.Reply (key opcode)) =>
        ret (FiniteCFG.packedTreeOutput ((port second reply).val, .unit))) := by
  let p := fixture opcode second
  have start : headFrom p.step p.states (p.start 0 packet) = .request (key opcode) (afterReply opcode second) := by
    cases opcode <;> fin_cases second <;> cbv
  have head : evaluate p.step (p.start 0 packet) =
      vis (.ask (key opcode)) (evaluate p.step ∘ afterReply opcode second) := by
    apply out_injective
    rw [out_evaluate _ _ p.mem_states, start, out_vis]
    rfl
  have tail (reply : signature.Reply (key opcode)) :
      evaluate p.step (afterReply opcode second reply) = pure ⟨⟨port second reply, ⟨⟩⟩⟩ := by
    apply out_injective
    change out (evaluate p.step (afterReply opcode second reply)) = out (ret _)
    change PUnit ⊕ PUnit at reply
    rw [out_evaluate _ _ p.mem_states, out_ret]
    dsimp [p]
    cases reply <;> cases opcode <;> fin_cases second <;> cbv
  rw [(packed opcode second).observe_eq packet env env (fun _ => rfl), Program.observe_eq, head]
  simp only [vis_bind, Function.comp_apply, tail, pure_bind]
  rfl

private abbrev sourceValid {opcode₁ opcode₂ : Bool} {second₁ second₂ : Fin 2}
    (left : Program.PackedEntry (fixture opcode₁ second₁) 0)
    (right : Program.PackedEntry (fixture opcode₂ second₂) 0) : Prop :=
  ∀ policy : Silmaril.Logic.ITree.Model.{0, 0} signature.traceSignature.toSignature,
    TraceInstitution.Sat policy (left.refinementSentence right .leftToRight env env env env)

private theorem valid_of_equal {S : Silmaril.Elgot.ITree.Signature}
    {l r : Tree S.Event (Nat × Value Atom)} (equal : l = r) :
    ∀ policy : Silmaril.Logic.ITree.Model.{0, 0} S,
      TraceInstitution.Sat (S := ⟨S⟩) policy ⟨_, l, HasTrace r⟩ :=
  (TraceInstitution.valid_hasTrace_iff (S := ⟨S⟩) l r).mpr (equal ▸ TraceLE.refl l)

-- The opcode keys collide. Every reply is still represented.
private def mergedKeys : Silmaril.Elgot.ITree.Signature := ⟨Event Unit (fun _ => Denote bit)⟩

private def mergeKeys : signature.traceSignature.toSignature ⟶ mergedKeys where
  request _ := ⟨Denote bit, .ask ()⟩
  reply
    | ⟨_, .ask _⟩ => id

example : ¬ Function.Injective mergeKeys.request := by
  intro injective
  have same : (⟨_, .ask (key false)⟩ : Request signature.traceSignature.toSignature.Event) =
      ⟨_, .ask (key true)⟩ := injective rfl
  let opcode : Request signature.traceSignature.toSignature.Event → Bool := fun
    | ⟨_, .ask k⟩ => k.1
  have impossible : false = true := congrArg opcode same
  cases impossible

example (q : Request signature.traceSignature.toSignature.Event) :
    Function.Bijective (mergeKeys.reply q) := by
  rcases q with ⟨_, event⟩
  cases event
  exact Function.bijective_id

example : ¬ sourceValid (packed false 1) (packed true 1) := by
  intro valid
  have accepted := (Program.refinementAt?_iff_valid_traceSat packet (packed false 1) (packed true 1)
    env env env env (fun _ => rfl) (fun _ => rfl)).mpr valid
  have rejected : (fixture false 1).refinementAt? (fixture true 1) 0 packet = false := by cbv
  simp [rejected] at accepted

example (policy : Silmaril.Logic.ITree.Model.{0, 0} mergedKeys) :
    TraceInstitution.Sat (S := ⟨mergedKeys⟩) policy
      ⟨_, (packed false 1).observeMapped mergeKeys env env, HasTrace ((packed true 1).observeMapped mergeKeys env env)⟩ := by
  apply valid_of_equal _ policy
  rw [Program.PackedEntry.observe_mapped, Program.PackedEntry.observe_mapped, packed_shape, packed_shape]
  erw [mergeKeys.tree_vis, mergeKeys.tree_vis]
  rfl

-- Keep the full keys, but the target can only return the first source reply.
private def firstReplyOnly : Silmaril.Elgot.ITree.Signature := ⟨Event signature.Request (fun _ => PUnit)⟩

private def restrictReply : signature.traceSignature.toSignature ⟶ firstReplyOnly where
  request
    | ⟨_, .ask k⟩ => ⟨PUnit, .ask k⟩
  reply
    | ⟨_, .ask _⟩ => fun _ => .inl ⟨⟩

example : Function.Injective restrictReply.request := by
  rintro ⟨_, left⟩ ⟨_, right⟩ same
  cases left with | ask left =>
  cases right with | ask right =>
  let keyOf : Request firstReplyOnly.Event → signature.Request := fun
    | ⟨_, .ask k⟩ => k
  have keys : left = right := congrArg keyOf same
  cases keys
  rfl

example : ¬ Function.Surjective (restrictReply.reply ⟨_, .ask (key false)⟩) := by
  intro onto
  obtain ⟨_, impossible⟩ := onto (.inr ⟨⟩)
  cases impossible

example : ¬ sourceValid (packed false 0) (packed false 1) := by
  intro valid
  have accepted := (Program.refinementAt?_iff_valid_traceSat packet (packed false 0) (packed false 1)
    env env env env (fun _ => rfl) (fun _ => rfl)).mpr valid
  have rejected : (fixture false 0).refinementAt? (fixture false 1) 0 packet = false := by cbv
  simp [rejected] at accepted

example (policy : Silmaril.Logic.ITree.Model.{0, 0} firstReplyOnly) :
    TraceInstitution.Sat (S := ⟨firstReplyOnly⟩) policy
      ⟨_, (packed false 0).observeMapped restrictReply env env,
        HasTrace ((packed false 1).observeMapped restrictReply env env)⟩ := by
  apply valid_of_equal _ policy
  rw [Program.PackedEntry.observe_mapped, Program.PackedEntry.observe_mapped, packed_shape, packed_shape]
  erw [restrictReply.tree_vis, restrictReply.tree_vis]
  rfl

section ReplyAliases

-- The key remains visible and each source reply has two target names.
private abbrev AliasedReply (k : signature.Request) := Bool × signature.Reply k
private def aliased : Silmaril.Elgot.ITree.Signature := ⟨Event signature.Request AliasedReply⟩

private def aliases : signature.traceSignature.toSignature ⟶ aliased where
  request
    | ⟨_, .ask k⟩ => ⟨AliasedReply k, .ask k⟩
  reply
    | ⟨_, .ask _⟩ => Prod.snd

private theorem aliases_keys : Function.Injective aliases.request := by
  rintro ⟨_, left⟩ ⟨_, right⟩ same
  cases left with | ask left =>
  cases right with | ask right =>
  let keyOf : Request aliased.Event → signature.Request := fun
    | ⟨_, .ask k⟩ => k
  have keys : left = right := congrArg keyOf same
  cases keys
  rfl

private theorem aliases_onto (q : Request signature.traceSignature.toSignature.Event) :
    Function.Surjective (aliases.reply q) := by
  rcases q with ⟨_, event⟩
  cases event
  exact fun reply => ⟨(false, reply), rfl⟩

example : ¬ Function.Injective (aliases.reply ⟨_, .ask (key false)⟩) := by
  intro injective
  have same : ((false, .inl ⟨⟩) : AliasedReply (key false)) = (true, .inl ⟨⟩) := injective rfl
  cases congrArg Prod.fst same

-- From the initial state the handler admits the true alias and moves to the
-- closed state. It denies the false alias of the same source reply.
private def aliasPolicy : Silmaril.Logic.ITree.Model.{0, 0} aliased where
  State := Bool
  initial state := state = false
  step
    | ⟨_, .ask _⟩, state, reply, next => state = false ∧ reply.1 = true ∧ next = true

private noncomputable def aliasSource : TraceInstitution.Sentence.{0, 1} signature.traceSignature :=
  (packed false 1).refinementSentence (packed false 1) .leftToRight env env env env

private theorem aliasSource_sat : TraceInstitution.Sat (aliasPolicy.reduct aliases) aliasSource :=
  valid_of_equal (l := (packed false 1).observe env env) rfl (aliasPolicy.reduct aliases)

example : (aliasSource.translateLift aliases).program = (packed false 1).observeMapped aliases env env :=
  ((packed false 1).observe_mapped aliases env env).symm

example : TraceInstitution.Sat aliasPolicy (aliasSource.translateLift aliases) :=
  (TraceInstitution.satisfaction_lift aliases aliases_keys aliasPolicy aliasSource).mpr aliasSource_sat

-- Extending the old single-trace image by choosing a section of the reply
-- projection would only translate exchanges to the false alias.
private def chooseFalse {A : Type 1} :
    Trace signature.traceSignature.toSignature.Event A → Trace aliased.Event A
  | .prefix => .prefix
  | .result a => .result a
  | .request (.ask k) => .request (.ask k)
  | .exchange (.ask k) reply tail => .exchange (.ask k) (false, reply) (chooseFalse tail)

private noncomputable def chosenSentence : TraceInstitution.Sentence.{0, 1} ⟨aliased⟩ :=
  ⟨aliasSource.Result, (packed false 1).observeMapped aliases env env,
    fun q => ∃ p, aliasSource.accepts p ∧ chooseFalse p = q⟩

private def trueTrace : Trace aliased.Event (Nat × Value Atom) :=
  .exchange (.ask (key false)) (true, .inl ⟨⟩) (.result (FiniteCFG.packedTreeOutput (0, .unit)))

private theorem trueTrace_handled :
    HandledTrace aliasPolicy.step false ((packed false 1).observeMapped aliases env env) trueTrace := by
  refine ⟨?_, ⟨true, ⟨rfl, rfl, rfl⟩, trivial⟩⟩
  rw [Program.PackedEntry.observe_mapped, packed_shape]
  erw [aliases.tree_vis]
  unfold trueTrace
  erw [hasTrace_vis_exchange_iff]
  erw [aliases.tree_ret]
  exact out_ret _

private def firstAlias {A : Type 1} : Trace aliased.Event A → Option Bool
  | .exchange (.ask _) reply _ => some reply.1
  | _ => none

example : ¬ TraceInstitution.Sat aliasPolicy chosenSentence := by
  intro sat
  obtain ⟨p, _, equal⟩ := sat false rfl trueTrace trueTrace_handled
  have aliasesEqual := congrArg firstAlias equal
  cases p with
  | «prefix» | result => cases aliasesEqual
  | request event => cases event; cases aliasesEqual
  | exchange event => cases event; cases aliasesEqual

-- The second arrow keeps both aliases of the first reply and omits all
-- aliases of the second. The composite therefore aliases and omits replies.
private def filtered : Silmaril.Elgot.ITree.Signature := ⟨Event signature.Request (fun _ => Bool)⟩

private def keepFirst : aliased ⟶ filtered where
  request
    | ⟨_, .ask k⟩ => ⟨Bool, .ask k⟩
  reply
    | ⟨_, .ask _⟩ => fun name => (name, .inl ⟨⟩)

private theorem keepFirst_keys : Function.Injective keepFirst.request := by
  rintro ⟨_, left⟩ ⟨_, right⟩ same
  cases left with | ask left =>
  cases right with | ask right =>
  let keyOf : Request filtered.Event → signature.Request := fun
    | ⟨_, .ask k⟩ => k
  have keys : left = right := congrArg keyOf same
  cases keys
  rfl

private abbrev originalObj : Silmaril.Elgot.ITree.Signature.InjectiveRequests := ⟨signature.traceSignature.toSignature⟩
private abbrev aliasedObj : Silmaril.Elgot.ITree.Signature.InjectiveRequests := ⟨aliased⟩
private abbrev filteredObj : Silmaril.Elgot.ITree.Signature.InjectiveRequests := ⟨filtered⟩
private def aliasArrow : originalObj ⟶ aliasedObj := ⟨aliases, aliases_keys⟩
private def firstArrow : aliasedObj ⟶ filteredObj := ⟨keepFirst, keepFirst_keys⟩

example : ¬ Function.Injective ((aliases ≫ keepFirst).reply ⟨_, .ask (key false)⟩) := by
  intro injective
  have same : false = true := injective rfl
  cases same

example : ¬ Function.Surjective ((aliases ≫ keepFirst).reply ⟨_, .ask (key false)⟩) := by
  intro onto
  obtain ⟨_, impossible⟩ := onto (.inr ⟨⟩)
  cases impossible

private def firstOnly (trace : Trace signature.traceSignature.toSignature.Event (Nat × Value Atom)) : Prop :=
  match trace with
  | .exchange (.ask _) reply _ =>
    match reply with
    | .inl _ => True
    | .inr _ => False
  | _ => True

private noncomputable def firstSentence : TraceInstitution.Sentence.{0, 1} signature.traceSignature :=
  ⟨_, (packed false 1).observe env env, firstOnly⟩

private def filteredPolicy : Silmaril.Logic.ITree.Model.{0, 0} filtered where
  State := Bool
  initial state := state = false
  step
    | ⟨_, .ask _⟩, state, name, next => state = false ∧ name = true ∧ next = true

private theorem firstSat : TraceInstitution.Sat (filteredPolicy.reduct (aliases ≫ keepFirst)) firstSentence := by
  intro x initial trace seen
  cases trace with
  | «prefix» | request | result => trivial
  | exchange event reply tail =>
    cases event
    cases reply with
    | inl => trivial
    | inr =>
      obtain ⟨_, ⟨_, impossible, _⟩, _⟩ := seen.2
      cases impossible

-- The intermediate model still offers the second source reply and reaches
-- the distinct ordered exit. The final reduct satisfies this same sentence.
example : ¬ TraceInstitution.Sat (aliasPolicy.reduct aliases) firstSentence := by
  let trace : Trace signature.traceSignature.toSignature.Event (Nat × Value Atom) :=
    .exchange (.ask (key false)) (.inr ⟨⟩) (.result (FiniteCFG.packedTreeOutput (1, .unit)))
  have seen : HandledTrace (aliasPolicy.reduct aliases).step false (packed false 1 |>.observe env env) trace := by
    refine ⟨?_, ⟨true, ⟨(true, .inr ⟨⟩), rfl, rfl, rfl, rfl⟩, trivial⟩⟩
    rw [packed_shape]
    exact (hasTrace_vis_exchange_iff _ _ _ _).mpr (out_ret _)
  exact fun sat => sat false rfl trace seen

private noncomputable abbrev liftInst := TraceInstitution.liftInstitution.{0, 1, 0}

example :
    liftInst.Sen.map (aliasArrow ≫ firstArrow) firstSentence =
      liftInst.Sen.map firstArrow (liftInst.Sen.map aliasArrow firstSentence) :=
  liftInst.Sen.map_comp_apply aliasArrow firstArrow firstSentence

example :
    ((liftInst.Mod.map (aliasArrow ≫ firstArrow).op).toFunctor.obj ⟨filteredPolicy⟩).as =
      (filteredPolicy.reduct keepFirst).reduct aliases :=
  Silmaril.Logic.ITree.Model.reduct_comp aliases keepFirst filteredPolicy

example : liftInst.Sat filteredObj ⟨filteredPolicy⟩ (liftInst.Sen.map (aliasArrow ≫ firstArrow) firstSentence) :=
  (liftInst.satisfaction (aliasArrow ≫ firstArrow) ⟨filteredPolicy⟩ firstSentence).mpr firstSat

-- The selected alias still executes the actual packed dispatcher and reaches
-- the first ordered result in the composed signature.
example : HandledTrace filteredPolicy.step false ((packed false 1).observeMapped (aliases ≫ keepFirst) env env)
    (.exchange (.ask (key false)) true (.result (FiniteCFG.packedTreeOutput (0, .unit)))) := by
  refine ⟨?_, ⟨true, ⟨rfl, rfl, rfl⟩, trivial⟩⟩
  rw [Program.PackedEntry.observe_mapped, packed_shape]
  erw [Silmaril.Elgot.ITree.Signature.Hom.tree_vis (aliases ≫ keepFirst), hasTrace_vis_exchange_iff,
    Silmaril.Elgot.ITree.Signature.Hom.tree_ret (aliases ≫ keepFirst)]
  exact out_ret _

private instance (k : signature.Request) :
    Fintype (((aliases ≫ keepFirst).request ⟨_, .ask k⟩).1) :=
  inferInstanceAs (Fintype Bool)

private def imageMask := signature.replyImageMask (aliases ≫ keepFirst)

example (key : signature.Request) : imageMask key (.inl ⟨⟩) = true := by rfl
example (key : signature.Request) : imageMask key (.inr ⟨⟩) = false := by rfl

private noncomputable def orderedComparison : TraceInstitution.Sentence.{0,1} signature.traceSignature :=
  (packed false 0).refinementSentence (packed false 1) .leftToRight env env env env

private theorem sourceRejects : (fixture false 0).refinementAt? (fixture false 1) 0 packet = false := by cbv

-- Aliasing alone preserves the rejection: a target handler may still
-- observe the second reply and distinguish the two ordered exits.
example : ¬ (∀ M : liftInst.Mod.obj (Opposite.op aliasedObj),
    liftInst.Sat aliasedObj M (liftInst.Sen.map aliasArrow orderedComparison)) := by
  intro valid
  have accepted := (Program.refinementAt?_iff_valid_liftSat aliasArrow aliases_onto packet
    (packed false 0) (packed false 1) env env env env (fun _ => rfl) (fun _ => rfl)).mpr valid
  simp [sourceRejects] at accepted

-- After omitting that reply, the executable image-filtered checker accepts
-- the same two packed graphs, and their translation is valid in every handler.
example (M : liftInst.Mod.obj (Opposite.op filteredObj)) :
    liftInst.Sat filteredObj M (liftInst.Sen.map (aliasArrow ≫ firstArrow) orderedComparison) := by
  have accepted : (fixture false 0).refinementAtUnder? imageMask (fixture false 1) 0 packet = true := by cbv
  exact (Program.refinementAtUnder?_iff_valid_liftSat (aliasArrow ≫ firstArrow) imageMask
    (signature.replyImageMask_iff (aliases ≫ keepFirst)) packet (packed false 0) (packed false 1)
    env env env env (fun _ => rfl) (fun _ => rfl)).mp accepted M

-- Keep only the true intermediate name for the first reply. Choosing the
-- false name before applying the second filter would lose that reply.
private def keepTrueFirst : aliased ⟶ filtered :=
  { keepFirst with
    reply := fun
      | ⟨_, .ask _⟩, _ => (true, .inl ⟨⟩) }

private def trueFirstArrow : aliasedObj ⟶ filteredObj := ⟨keepTrueFirst, keepFirst_keys⟩

private instance finiteAliases (k : signature.Request) :
    Fintype ((aliases.request ⟨_, .ask k⟩).1) :=
  inferInstanceAs (Fintype (AliasedReply k))

private instance (k : signature.Request) :
    Fintype (((aliases ≫ keepTrueFirst).request ⟨_, .ask k⟩).1) :=
  inferInstanceAs (Fintype Bool)

private def secondFilter (k : signature.Request) (reply : AliasedReply k) : Bool :=
  letI : DecidableEq (AliasedReply k) := inferInstanceAs (DecidableEq (Bool × Denote bit))
  let backward : Bool → AliasedReply k := keepTrueFirst.reply (aliases.request ⟨_, .ask k⟩)
  decide (∃ targetReply : Bool, backward targetReply = reply)

private theorem secondFilter_exact (k : signature.Request) (reply : AliasedReply k) :
    secondFilter k reply = true ↔
      ∃ targetReply, keepTrueFirst.reply (aliases.request ⟨_, .ask k⟩) targetReply = reply := by
  simp only [secondFilter, decide_eq_true_eq]
  rfl

private def projected := signature.projectReplyMask aliases secondFilter
private def direct := signature.replyImageMask (aliases ≫ keepTrueFirst)

example : secondFilter (key false) (false, .inl ⟨⟩) = false := by rfl
example : secondFilter (key false) (true, .inl ⟨⟩) = true := by rfl
example : projected (key false) (.inl ⟨⟩) = true := by rfl
example : projected (key false) (.inr ⟨⟩) = false := by rfl

private theorem mask_agrees : projected = direct :=
  PrimitiveSignature.projectReplyMask_eq_comp aliases keepTrueFirst secondFilter secondFilter_exact

example :
    (fixture false 0).refinementAtUnder? projected (fixture false 1) 0 packet =
      (fixture false 0).refinementAtUnder? direct (fixture false 1) 0 packet ∧
    (fixture false 0).refinementUnder? projected (fixture false 1) =
      (fixture false 0).refinementUnder? direct (fixture false 1) := by
  rw [mask_agrees]
  exact ⟨rfl, rfl⟩

private theorem stagedAtAccepts : (fixture false 0).refinementAtUnder? projected (fixture false 1) 0 packet = true := by cbv
private theorem stagedInterfaceAccepts : (fixture false 0).refinementUnder? projected (fixture false 1) = true := by cbv
example : (fixture false 0).refinement? (fixture false 1) = false := by cbv

private def entryAt (port : Fin 2) (input : Fin 1) : Program.PackedEntry (fixture false port) input := by
  have zero : input = 0 := Subsingleton.elim _ _
  subst input
  exact packed false port

private theorem agreesAt (port : Fin 2) (input : Fin 1) (pkt : Denote (inputs input)) :
    (entryAt port input).recordAgrees pkt env := by
  have zero : input = 0 := Subsingleton.elim _ _
  subst input
  exact fun _ => rfl

example : liftInst.Sat aliasedObj
    ⟨(TraceInstitution.allRepliesModel ⟨filtered⟩).reduct keepTrueFirst⟩
    (liftInst.Sen.map aliasArrow orderedComparison) := by
  exact (Program.refinementAtUnder?_iff_staged_liftSat aliasArrow trueFirstArrow (finiteMid := finiteAliases)
    secondFilter secondFilter_exact packet (packed false 0) (packed false 1)
    env env env env (fun _ => rfl) (fun _ => rfl)).mp stagedAtAccepts

example (input : Fin 1) (pkt : Denote (inputs input)) (M : liftInst.Mod.obj (Opposite.op filteredObj)) :
    liftInst.Sat filteredObj M (liftInst.Sen.map (aliasArrow ≫ trueFirstArrow)
      ((entryAt 0 input).refinementSentence (entryAt 1 input) .leftToRight env env env env)) := by
  let sentence := (entryAt 0 input).refinementSentence (entryAt 1 input) .leftToRight env env env env
  have staged := (Program.refinementUnder?_iff_staged_liftSat aliasArrow trueFirstArrow (finiteMid := finiteAliases)
    secondFilter secondFilter_exact (entryAt 0) (entryAt 1) env env (fun _ _ => env) (fun _ _ => env)
    (agreesAt 0) (agreesAt 1)).mp stagedInterfaceAccepts input pkt
  let all := TraceInstitution.allRepliesModel ⟨filtered⟩
  have final := (liftInst.satisfaction trueFirstArrow ⟨all⟩ (liftInst.Sen.map aliasArrow sentence)).mpr staged
  have valid := (TraceInstitution.liftInstitution_valid_iff filteredObj _).mpr final M
  erw [← liftInst.Sen.map_comp_apply aliasArrow trueFirstArrow] at valid
  exact valid

end ReplyAliases

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
