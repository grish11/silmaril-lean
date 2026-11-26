module

import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Thms
import Mathlib.Tactic.FinCases
meta import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Defs

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

open Silmaril.Elgot.ITree
open Silmaril.Elgot.ITree.Finite (Event evaluate headFrom out_evaluate)
open Silmaril.Isotope (BoundCtx Value)
open Silmaril.Isotope.Bridge.NamedFlat (elaborate check_sound)
open Silmaril.Isotope.LambdaSSA

private def signature : PrimitiveSignature Unit :=
  ⟨fun _ => .unit, fun _ => .unit⟩

private def inputs : Fin 1 → PacketType := fun _ => .unit
private def outputs : Fin 2 → PacketType := fun _ => .unit
private def locals : Fin 2 → PacketType := fun _ => .unit

-- Both graphs expose and complete the same request. The continuation
-- either loops silently or returns unit at a specified ordered exit.
private def fixture (exit : Option (Fin 2)) : Program signature inputs outputs where
  locals := 2
  localType := locals
  entry _ := .inl 0
  entryType _ := rfl
  block i := Fin.cases (.apply () .unit (.inl 1) .unit)
    (fun _ => match exit with
      | none => .term (.jump (.inl 1) .unit)
      | some port => .term (.jump (.inr port) .unit)) i

private abbrev looping := fixture none
private abbrev returning (port : Fin 2) := fixture (some port)
private def packet : Denote (inputs 0) := ⟨⟩
private def key : signature.Request := ⟨(), ⟨⟩⟩

private def exchangePrefix : Program.ObservationTrace signature :=
  .exchange (.ask key) ⟨⟩ .prefix

private theorem hasExchangePrefix : HasTrace (looping.observe 0 packet) exchangePrefix := by
  let next : signature.Reply key → looping.State := by
    change signature.Reply key → ULift (PacketAt (Sum.elim locals outputs))
    exact fun _ => ⟨⟨.inl 1, ⟨⟩⟩⟩
  have head : headFrom looping.step looping.states (looping.start 0 packet) = .request key next := by cbv
  have root : evaluate looping.step (looping.start 0 packet) = vis (.ask key) (evaluate looping.step ∘ next) := by
    apply out_injective
    rw [out_evaluate _ _ looping.mem_states, head, out_vis]
    rfl
  rw [Program.observe_eq, root, vis_bind]
  exact ⟨_, out_vis _ _, trivial⟩

private def captures : Fin 1 → Register := fun _ => ⟨0⟩
private def context : BoundCtx PacketType 1 := .snoc .nil .unit
private instance : Silmaril.HasTy Unit PacketType := signature.typing

private theorem admits (exit : Option (Fin 2)) (input : Fin 1) :
    (elaborate ((fixture exit).compile input) (fixture exit).exits captures).isSome := by
  fin_cases input
  cases exit with
  | none => decide
  | some port => fin_cases port <;> decide

private def target (exit : Option (Fin 2)) (input : Fin 1) :=
  (elaborate ((fixture exit).compile input) (fixture exit).exits captures).get (admits exit input)

private def packed (exit : Option (Fin 2)) (input : Fin 1) : Program.PackedEntry (fixture exit) input where
  count := 1
  captures := captures
  context := context
  blocks := locals
  exits := outputs
  target := target exit input
  accepted := Option.eq_some_of_isSome (admits exit input)
  typed := check_sound _ _ _ _ (by
    fin_cases input
    cases exit with
    | none => decide
    | some port => fin_cases port <;> decide)

private def env : Semantics.Env Atom := fun _ => .unit

private theorem agrees (exit : Option (Fin 2)) (input : Fin 1) (packet : Denote (inputs input)) :
    (packed exit input).recordAgrees packet env :=
  fun _ => rfl

private noncomputable abbrev satisfies :=
  Silmaril.Logic.ITree.TraceInstitution.institution.{0, 1, 0}.Sat signature.traceSignature
    ⟨signature.traceModel⟩

example : HandledTrace signature.traceModel.step () ((packed none 0).observe env env) exchangePrefix := by
  rw [signature.handledTrace_iff, (packed none 0).observe_eq packet env env (agrees none 0 packet)]
  exact (hasTrace_bind_pure_map_iff
    Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Program.packedTreeOutput_injective
    _ exchangePrefix).mpr hasExchangePrefix

example (trace : Program.ObservationTrace signature) :
    HandledTrace signature.traceModel.step ()
      (diverge : Tree (Event signature.Request signature.Reply) (Nat × Value Atom)) trace ↔ trace = .prefix :=
  (signature.handledTrace_iff _ _).trans (hasTrace_diverge_iff trace)

example : satisfies ((packed none 0).refinementSentence (packed (some 0) 0) .leftToRight env env env env) :=
  (Program.refinement?_iff_traceSat (packed none) (packed (some 0)) env env
    (fun _ _ => env) (fun _ _ => env) (agrees none) (agrees (some 0))).mp (by cbv) 0 packet

example : ¬ satisfies ((packed none 0).refinementSentence (packed (some 0) 0) .rightToLeft env env env env) := by
  intro sat
  have pass := (Program.refinementAt?_iff_traceSat packet (packed (some 0) 0) (packed none 0) env env env env
    (agrees (some 0) 0 packet) (agrees none 0 packet)).mpr sat
  have rejected : (returning 0).refinementAt? looping 0 packet = false := by cbv
  simp [rejected] at pass

example : looping.weakEq? (returning 0) = false := by cbv

-- Equal payloads at different exit positions still fail directed refinement.
example :
    ¬ satisfies ((packed (some 0) 0).refinementSentence (packed (some 1) 0) .leftToRight env env env env) := by
  intro sat
  have pass := (Program.refinementAt?_iff_traceSat packet (packed (some 0) 0) (packed (some 1) 0) env env env env
    (agrees (some 0) 0 packet) (agrees (some 1) 0 packet)).mpr sat
  have rejected : (returning 0).refinementAt? (returning 1) 0 packet = false := by cbv
  simp [rejected] at pass

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
