module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.Thms
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Thms
meta import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Defs

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.Examples

open LambdaSSA (FiniteCFG Flat)
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction (region)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
  (Atom Denote PacketType PrimitiveSignature Program)
open Silmaril.Elgot (iter liftPure)
open Silmaril.Elgot.ITree (Tree ret diverge diverge_bind iterate_fixpoint iterate_forever iterate_uniformity)
open Silmaril.Elgot.ITree.Finite (Event evaluate transition)

private inductive Op where
  | first | second | third
  deriving DecidableEq

private def inputType : PacketType := .product .unit .unit
private def bit : PacketType := .coprod .unit .unit

private def sig : PrimitiveSignature Op where
  argument
    | .first => inputType
    | .second => bit
    | .third => .product bit inputType
  reply
    | .first => bit
    | .second => .unit
    | .third => bit

private def packets (i : Fin 3) : PacketType := if i.val = 1 then inputType else .unit
private def outputs (i : Fin 2) : PacketType := if i.val = 0 then .unit else .product bit bit

-- The third request uses both the entry packet and the first reply.
-- The second declared exit returns the first and third replies.
private def requests {captures : Nat} : Flat Op 5 (captures + 1) :=
  .let₁ (.op .first (.bv 0)) (.let₁ (.op .second (.bv 0))
    (.let₁ (.op .third (.pair (.bv 1) (.bv 2))) (.br 4 (.pair (.bv 2) (.bv 0)))))

private def original : FiniteCFG Op 3 2 0 where
  entry := .br 0 .unit
  block i :=
    if i.val = 0 then .br 1 (.pair (.bv 0) .unit)
    else if i.val = 1 then requests
    else .br 3 .unit

private def checked : Checked sig .nil packets outputs original :=
  (check sig .nil packets outputs original (some 1)).get (by decide)

private def built :=
  (construct sig (fun i => (checked.shape.table i).1) outputs checked.emitted.code).get (by decide)

private def dispatcher := built.program

example : checked.shape.selected.val = 1 := rfl
example : checked.shape.row.requests = 3 := rfl
example : dispatcher.locals = 6 := rfl
example : (checked.emitted.code.block 0).erase = .br 1 (.pair (.var 0) .unit) := rfl
example : (checked.emitted.code.block 2).erase = .br 6 .unit := rfl

private def inputPacket : Denote inputType := (⟨⟩, ⟨⟩)
private def initial : dispatcher.State := by
  refine ⟨⟨.inl ⟨1, by decide⟩, ?_⟩⟩
  exact inputPacket

private def askFirst : sig.Request := ⟨.first, inputPacket⟩
private def askSecond (value : Denote bit) : sig.Request := ⟨.second, value⟩
private def askThird (value : Denote bit) : sig.Request := ⟨.third, (value, inputPacket)⟩

private def afterFirst (first : Denote bit) : dispatcher.State := by
  refine ⟨⟨.inl ⟨3, by decide⟩, ?_⟩⟩
  change Denote inputType × Denote bit
  exact (inputPacket, first)

private def afterSecond (first : Denote bit) : dispatcher.State := by
  refine ⟨⟨.inl ⟨4, by decide⟩, ?_⟩⟩
  change (Denote inputType × Denote bit) × PUnit
  exact ((inputPacket, first), ⟨⟩)

private def afterThird (first third : Denote bit) : dispatcher.State := by
  refine ⟨⟨.inl ⟨5, by decide⟩, ?_⟩⟩
  change ((Denote inputType × Denote bit) × PUnit) × Denote bit
  exact (((inputPacket, first), ⟨⟩), third)

private def returned (first third : Denote bit) : dispatcher.State :=
  ⟨⟨.inr 1, (first, third)⟩⟩

example : dispatcher.step (dispatcher.start 0 ⟨⟩) = .inr initial := rfl
example : dispatcher.step initial = .inl (.request askFirst afterFirst) := rfl
example (first : Denote bit) :
    dispatcher.step (afterFirst first) = .inl (.request (askSecond first) fun _ => afterSecond first) := rfl
example (first : Denote bit) :
    dispatcher.step (afterSecond first) = .inl (.request (askThird first) (afterThird first)) := rfl
example (first third : Denote bit) : dispatcher.step (afterThird first third) = .inr (returned first third) := rfl

private def emptyEnv : Env Atom := fun _ => .unit

private theorem codec_id (value : Value Atom) : valueCodec id value = value := by
  induction value <;> simp_all only [valueCodec, id_eq]

private theorem primitiveAgreement : PrimitivesAgree sig.primitive sig.primitive id := by
  intro op value
  rw [codec_id, show valueCodec (id : Atom → Atom) = id from funext codec_id, id_map]

private theorem resultCodec_identity : resultCodec (id : Atom → Atom) = id := by
  funext out
  cases out
  simp only [resultCodec, codec_id, id_eq]

theorem packed_observation :
    (region sig.primitive emptyEnv original.erase >>= fun out => pure (FiniteCFG.packedTreeOutput out)) =
      built.packed.observe emptyEnv emptyEnv := by
  simpa only [resultCodec_identity, id_map] using
    checked.emitted.public_run built emptyEnv emptyEnv emptyEnv id primitiveAgreement rfl

theorem dispatcher_observation :
    (region sig.primitive emptyEnv original.erase >>= fun out => pure (FiniteCFG.packedTreeOutput out)) =
      (dispatcher.observe 0 ⟨⟩ >>= fun out => pure (FiniteCFG.packedTreeOutput out)) :=
  packed_observation.trans (built.packed.observe_eq ⟨⟩ _ _ (fun _ => rfl))

-- The entry's case selects the request prefix, a direct ordered return,
-- or an unchanged self-loop. The original and public runs are checked
-- under the same encoded choice.
private def choiceType : PacketType := .coprod .unit (.coprod .unit .unit)

private def branchPackets (i : Fin 3) : PacketType :=
  if i.val = 0 then choiceType else packets i

private def branching : FiniteCFG Op 3 2 1 where
  entry := .br 0 (.bv 0)
  block i :=
    if i.val = 0 then .case (.bv 0) (.br 1 (.pair .unit .unit))
      (.case (.bv 0) (.br 3 .unit) (.br 2 .unit))
    else if i.val = 1 then requests
    else .br 2 .unit

private def branchingChecked : Checked sig (.snoc .nil choiceType) branchPackets outputs branching :=
  (check sig (.snoc .nil choiceType) branchPackets outputs branching (some 1)).get (by decide)

-- A pure tail can itself be an old-label self-jump.
example : (check sig (.snoc .nil choiceType) branchPackets outputs branching (some 2)).isSome = true := rfl

private def branchingBuilt :=
  (construct sig (fun i => (branchingChecked.shape.table i).1) outputs branchingChecked.emitted.code).get (by decide)

private def branches := branchingBuilt.program

private def encodedChoice (choice : Denote choiceType) : Env Atom := fun _ => choiceType.encode choice
private def take : Denote choiceType := .inl ⟨⟩
private def bypass : Denote choiceType := .inr (.inl ⟨⟩)
private def spin : Denote choiceType := .inr (.inr ⟨⟩)

private def takeState : branches.State := by
  refine ⟨⟨.inl ⟨1, by decide⟩, ?_⟩⟩
  exact inputPacket

private def bypassState : branches.State := ⟨⟨.inr 0, ⟨⟩⟩⟩

private def spinState : branches.State := by
  refine ⟨⟨.inl ⟨2, by decide⟩, ?_⟩⟩
  change PUnit
  exact ⟨⟩

example : branches.step (branches.start 0 take) = .inr takeState := rfl
example : ∃ next, branches.step takeState = .inl (.request askFirst next) := ⟨_, rfl⟩
private theorem bypass_step : branches.step (branches.start 0 bypass) = .inr bypassState := rfl
private theorem spin_step : branches.step (branches.start 0 spin) = .inr spinState := rfl
private theorem self_step : branches.step spinState = .inr spinState := rfl

theorem branching_packed (choice : Denote choiceType) :
    (region sig.primitive (encodedChoice choice) branching.erase >>=
      fun out => pure (FiniteCFG.packedTreeOutput out)) =
      branchingBuilt.packed.observe emptyEnv (encodedChoice choice) := by
  simpa only [resultCodec_identity, id_map] using
    branchingChecked.emitted.public_run branchingBuilt (encodedChoice choice) emptyEnv (encodedChoice choice)
      id primitiveAgreement (codec_id _).symm

theorem branching_observation (choice : Denote choiceType) :
    (region sig.primitive (encodedChoice choice) branching.erase >>=
      fun out => pure (FiniteCFG.packedTreeOutput out)) =
      (branches.observe 0 choice >>= fun out => pure (FiniteCFG.packedTreeOutput out)) :=
  (branching_packed choice).trans (branchingBuilt.packed.observe_eq choice _ _ (fun _ => rfl))

private theorem ret_eq_pure {A : Type 1} (value : A) :
    ret (E := Event sig.Request sig.Reply) value = pure value := rfl

private theorem evaluate_jump {here next : branches.State} (jump : branches.step here = .inr next) :
    evaluate branches.step here = evaluate branches.step next := by
  unfold evaluate
  rw [congrFun (iterate_fixpoint (transition branches.step)) here]
  simp only [transition, jump, ret_eq_pure, pure_bind, Sum.elim_inr]

private theorem bypass_returns : branches.observe 0 bypass = pure (0, .unit) := by
  rw [branches.observe_eq 0 bypass, evaluate_jump bypass_step, evaluate,
    congrFun (iterate_fixpoint (transition branches.step)) bypassState]
  have terminal : branches.step bypassState = .inl (.result ⟨⟨0, ⟨⟩⟩⟩) := rfl
  simp [transition, terminal, ret_eq_pure, Program.renderResult, outputs, PacketType.encode]

theorem original_bypass :
    (region sig.primitive (encodedChoice bypass) branching.erase >>=
      fun out => pure (FiniteCFG.packedTreeOutput out)) =
      pure (FiniteCFG.packedTreeOutput (0, .unit)) := by
  rw [branching_observation, bypass_returns, pure_bind]

private theorem spin_diverges : branches.observe 0 spin = diverge := by
  rw [branches.observe_eq 0 spin, evaluate_jump spin_step]
  let forever : PUnit.{2} → Tree (Event sig.Request sig.Reply) (Program.Result outputs ⊕ PUnit.{2}) :=
    fun _ => pure (.inr ⟨⟩)
  have square := iterate_uniformity forever (transition branches.step) (fun _ => spinState) (by
    funext p
    simp [Bind.kleisliRight, liftPure, forever, transition, self_step, ret_eq_pure])
  have loop : evaluate branches.step spinState = iter forever PUnit.unit := by
    simpa only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind, evaluate] using
      (congrFun square PUnit.unit).symm
  rw [loop, show iter forever PUnit.unit = diverge from iterate_forever PUnit.unit, diverge_bind]

theorem unchanged_cycle :
    (region sig.primitive (encodedChoice spin) branching.erase >>=
      fun out => pure (FiniteCFG.packedTreeOutput out)) = diverge ∧
      branchingBuilt.packed.observe emptyEnv (encodedChoice spin) = diverge := by
  have source : (region sig.primitive (encodedChoice spin) branching.erase >>=
      fun out => pure (FiniteCFG.packedTreeOutput out)) = diverge := by
    rw [branching_observation, spin_diverges, diverge_bind]
  exact ⟨source, (branching_packed spin).symm.trans source⟩

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.Examples
