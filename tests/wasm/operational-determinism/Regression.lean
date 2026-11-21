module

import Silmaril.Wasm.Execution.Core.Entry.Determinism.Thms
import Silmaril.Wasm.Numerics.Float

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Execution.Core.Entry
  Silmaril.Wasm.Numerics Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Det
  Silmaril.Wasm.SingleThreaded.Exec Silmaril.Semantics.Operational

private def machine (P : Profile) := ordinary P (noHost : HostSemantics Empty)
private def bubble : Config Empty := ⟨{}, {}, vals [.i32 3, .i32 4] ++ [.trap]⟩
private def intermediate : Config Empty := ⟨{}, {}, vals [.i32 3] ++ [.trap]⟩
private def trapped : Config Empty := ⟨{}, {}, [.trap]⟩

private theorem large (P : Profile) : (machine P).step bubble trapped :=
  Step.trapInstrs (vs := [.i32 3, .i32 4]) (rest := []) (.inl (by simp))

private theorem small (P : Profile) : (machine P).step bubble intermediate :=
  Step.ctxtInstrs (vs := [.i32 3]) (rest := [])
    (Step.trapInstrs (vs := [.i32 4]) (rest := []) (.inl (by simp))) (.inl (by simp))

example (oracle : GrowOracle) : ¬ (machine (profile oracle)).StepDetAt bubble := by
  intro det
  have same := congrArg (fun state : Config Empty => state.code.length) (det (large _) (small _))
  cases same

example (oracle : GrowOracle) : (machine (profile oracle)).ResultDetAt bubble :=
  deterministic_result oracle bubble

example (oracle : GrowOracle) : (WithUB.ofOpSem (machine (profile oracle))).requireLocalDet.ub bubble :=
  .inr fun det => by
    have same := congrArg (fun state : Config Empty => state.code.length) (det.1 (large _) (small _))
    cases same

example (oracle : GrowOracle) :
    ((WithUB.ofOpSem (machine (profile oracle))).requireViewDet some).toOpSem.May bubble .trap := by
  have det := deterministic_result oracle bubble
  apply (WithUB.enforce_may_iff (fun {_} path => det.of_reach path)).mpr
  exact ⟨trapped, .single (large _), .trap, rfl, rfl⟩

private def absent : HeadFn Empty := fun _ _ _ _ => none

private def trappingOracle (oracle : GrowOracle) : Oracle (WithUB.ofOpSem (machine (profile oracle))) :=
  driverOracle absent (by
    intro source target run
    exact step?_sound (Inv := fun _ _ => True) (by intro _ _ _ _ _ _ impossible; cases impossible)
      rfl (deepAll_true source.frame source.code) run)

private theorem bubbleDecision : (trappingOracle neverFail).pick bubble = .move trapped := by
  have split : splitVals bubble.code = ([.i32 3, .i32 4], [.trap]) := rfl
  rw [trappingOracle, driverOracle_pick]
  unfold driverDecision
  have notFinal : bubble.outcome? = none := rfl
  rw [notFinal, step?_cons split]
  rfl

example : (trappingOracle neverFail).run bubble 0 = .exhausted bubble := by
  rw [Oracle.run, bubbleDecision]

example : (trappingOracle neverFail).run bubble 1 = .stop trapped (.observed .trap) := by
  rw [Oracle.run, bubbleDecision]
  change (trappingOracle neverFail).run trapped 0 = _
  have decided : (trappingOracle neverFail).pick trapped = .stop (.observed .trap) := by
    rw [trappingOracle, driverOracle_pick]
    rfl
  rw [Oracle.run, decided]

private def nanPlus : BitVec 32 := 0x7fc00000
private def nanMinus : BitVec 32 := 0xffc00000
private def floatVal (bits : BitVec 32) : Val := .num ⟨.float .f32, bits⟩
private def resultBits : Intrinsic.Completion → Nat
  | .ok [.num ⟨_, bits⟩] => bits.toNat
  | _ => 0
private def addNaN : Config Empty :=
  ⟨{}, {}, [(.plain (.floatConst .f32 nanPlus)), .plain (.floatConst .f32 0), .plain (.floatBinOp .f32 .add)]⟩

private theorem nan_result (nd : Bool) {bits : BitVec 32} (admitted : floatBinOpRel .f32 .add nanPlus 0 bits) :
    (machine (Profile.spec nd)).May addNaN (.returned (.ok [floatVal bits])) :=
  ⟨⟨{}, {}, [.plain (.floatConst .f32 bits)]⟩,
    .single (.numeric (.floatBinOp admitted)), .values [floatVal bits], rfl, rfl⟩

private theorem nonTrapAmbiguous (nd : Bool) : ¬ (machine (Profile.spec nd)).NonTrapDetAt addNaN := by
  intro det
  have left := nan_result nd (bits := nanPlus) (by unfold floatBinOpRel; decide +kernel)
  have right := nan_result nd (bits := nanMinus) (by unfold floatBinOpRel; decide +kernel)
  have same := OpSem.nonTrapDetAt_iff.mp det left right
  have distinct : nanPlus.toNat ≠ nanMinus.toNat := by decide
  exact distinct (congrArg resultBits same)

example (nd : Bool) :
    ((WithUB.ofOpSem (machine (Profile.spec nd))).requireViewDet OpSem.returnView).ub addNaN :=
  .inr (nonTrapAmbiguous nd)

example (oracle : GrowOracle) : (machine (profile oracle)).ResultDetAt addNaN :=
  deterministic_result oracle addNaN

#print axioms driverOracle
#print axioms deterministic_result
#print axioms profileFree_steps
#print axioms profileFree_result
#print axioms Intrinsic.State.raw_may_iff_bounded
