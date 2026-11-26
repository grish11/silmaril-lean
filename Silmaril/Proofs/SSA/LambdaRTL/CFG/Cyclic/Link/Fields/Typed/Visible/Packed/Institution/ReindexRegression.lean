module

import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Reindex.Thms
import Silmaril.Semantics.ITree.Signature.Execution.Thms
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

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
