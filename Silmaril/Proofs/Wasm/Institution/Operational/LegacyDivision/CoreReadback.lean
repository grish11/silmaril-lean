module

public import Silmaril.Wasm.Institution.Operational.LegacyDivision.Core.Thms
public import Silmaril.Wasm.Institution.Operational.LegacyDivision.Thms
public import Silmaril.Wasm.Institution.Operational.Division.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.LegacyDivision.Proofs

open Silmaril.Semantics.SOS
open Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Runtime (AdminInstr Value)
open Silmaril.Wasm.SingleThreaded.Det (noHost)

variable {I H : Type} {S : Syntax I} (E : CoreEncoding S)

private def replayValue : Val → Value
  | .num v => ⟨v.type, v.bits⟩
  | _ => .int .i32 0

-- The total function is internal. Readback begins in the emitted image, and
-- its image invariant forces the returned code to emit to the exact target.
private def replay (S : Syntax I) (a : Admin) : AdminInstr I :=
  match a.val? with
  | some v => S.value (replayValue v)
  | none =>
    match a with
    | .plain (.intBinOp t (.div k)) => S.divide t k
    | .plain .nop => S.nop
    | _ => .trap

@[simp] private theorem replay_value (v : Val) :
    replay S v.toAdmin = S.value (replayValue v) := by simp [replay]

@[simp] private theorem replay_liftValue (v : Value) :
    replay S (liftValue v).toAdmin = S.value v := by
  rw [replay_value]
  rfl

@[simp] private theorem replay_const (t : IntType) (x : IntValue t) :
    replay S (Division.intConst t x) = S.value (.int t x) :=
  replay_liftValue (.int t x)

@[simp] private theorem replay_div (t : IntType) (k : Signedness) :
    replay S (Division.divOp t k) = S.divide t k := rfl

@[simp] private theorem replay_nop : replay S (.plain .nop) = S.nop := rfl
@[simp] private theorem replay_trap : replay S .trap = .trap := rfl

@[simp] private theorem replay_values (vs : List Val) :
    (vals vs).map (replay S) = S.values (vs.map replayValue) := by
  simp [vals, Syntax.values, List.map_map, Function.comp_def]

private theorem replay_admitted {code : List Admin} (ok : Division.AdmittedCode code) :
    Admitted S (code.map (replay S)) := by
  intro a member
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp member
  have supported := ok b hb
  cases supported <;> simp

private def Image (code : List Admin) : Prop :=
  ∀ a ∈ code, emitAdmin E.emit (replay S a) = some a

private theorem emitted_admin {a : AdminInstr I} (h : Allowed S a) :
    ∃ b, emitAdmin E.emit a = some b ∧ replay S b = a ∧ Division.Allowed b := by
  cases h with
  | value v => exact ⟨_, E.value v, replay_liftValue v, .value (liftValue v)⟩
  | divide t k => exact ⟨_, E.divide t k, rfl, .division t k⟩
  | nop => exact ⟨_, E.nop, rfl, .nop⟩
  | trap => exact ⟨_, rfl, rfl, .trap⟩

private theorem emit_properties {code : List (AdminInstr I)} (ok : Admitted S code) :
    Division.AdmittedCode (emitCode E.emit code) ∧ Image E (emitCode E.emit code) ∧
      (emitCode E.emit code).map (replay S) = code := by
  induction code with
  | nil => simp [Division.AdmittedCode, Image, emitCode]
  | cons a tail ih =>
    obtain ⟨ha, ht⟩ := admitted_cons.mp ok
    obtain ⟨b, emits, rfl, supported⟩ := emitted_admin E ha
    obtain ⟨tailSupported, tailImage, tailRound⟩ := ih ht
    have expanded : emitCode E.emit (replay S b :: tail) = b :: emitCode E.emit tail := by
      simp [emitCode, emits]
    rw [expanded]
    exact ⟨List.forall_mem_cons.mpr ⟨supported, tailSupported⟩,
      List.forall_mem_cons.mpr ⟨emits, tailImage⟩, congrArg (List.cons (replay S b)) tailRound⟩

private theorem emit_replay {code : List Admin} (h : Image E code) :
    emitCode E.emit (code.map (replay S)) = code := by
  induction code with
  | nil => rfl
  | cons a tail ih =>
    obtain ⟨head, rest⟩ := List.forall_mem_cons.mp h
    have same := ih rest
    simpa only [List.map_cons, emitCode, List.filterMap_cons, head] using congrArg (List.cons a) same

private theorem image_const (t : IntType) (x : IntValue t) :
    Image E [Division.intConst t x] := by
  simp [Image, E.value, liftValue, Value.int, Val.toAdmin]

private theorem core_image {a b : Config H} (path : Division.DerivesEdge a b) :
    Image E a.code → Image E b.code :=
  Derives.least (M := fun j => Image E j.1.code → Image E j.2.code) path (by
    intro r member ih
    change Division.RuleInstance H r at member
    cases member with
    | divide _ _ t k x y _ _ => exact fun _ => image_const E t (Division.quotient t k x y)
    | context s f vs before after tail _ _ =>
      intro supported
      change Image E (vals vs ++ before ++ tail) at supported
      change Image E (vals vs ++ after ++ tail)
      simp only [Image, List.forall_mem_append] at supported ⊢
      exact ⟨⟨supported.1.1, ih (Division.codeEdge s f before after) (List.Mem.head _) supported.1.2⟩,
        supported.2⟩
    | _ => intro _; simp [Division.codeEdge, Image, emitAdmin])

private theorem core_world {a b : Config H} (edge : Division.DerivesEdge a b) :
    a.store = b.store ∧ a.frame = b.frame :=
  Derives.least (M := fun j => j.1.store = j.2.store ∧ j.1.frame = j.2.frame) edge (by
    intro r member _
    change Division.RuleInstance H r at member
    cases member <;> exact ⟨rfl, rfl⟩)

private theorem divide_result (t : IntType) (k : Signedness) (x y : IntValue t)
    (nonzero : y ≠ 0) (noOverflow : ¬ Division.Overflows t k x y) :
    intBinOp t (.div k) x y = .ok (Division.quotient t k x y) := by
  cases k with
  | unsigned => rw [intBinOp, ite_eq_right nonzero]; rfl
  | signed =>
    rw [intBinOp, ite_eq_right nonzero, ite_eq_right (fun h => noOverflow ⟨rfl, h⟩)]
    rfl

private theorem replay_bubble {vs : List Val} {tail : List Admin}
    (nonempty : vs ≠ [] ∨ tail ≠ []) (admitted : Division.AdmittedCode tail) :
    DerivesEdge S ((vals vs ++ [Admin.trap] ++ tail).map (replay S)) [AdminInstr.trap] := by
  have tailOk := replay_admitted (S := S) admitted
  cases vs with
  | nil =>
    cases tail with
    | nil => exact (nonempty.elim (fun h => h rfl) (fun h => h rfl)).elim
    | cons a tail =>
      exact derives_redex (.trapTail (replay S a) (tail.map (replay S)) tailOk)
  | cons v vs =>
    simpa only [List.map_append, replay_values, List.map_cons, List.map_nil, replay_trap] using
      derives_redex (S := S) (.trapValues (replayValue v) (vs.map replayValue) (tail.map (replay S)) tailOk)

private theorem replay_derives {a b : Config H} (edge : Division.DerivesEdge a b) :
    DerivesEdge S (a.code.map (replay S)) (b.code.map (replay S)) :=
  Derives.least (M := fun j => DerivesEdge S (j.1.code.map (replay S)) (j.2.code.map (replay S)))
    edge (by
      intro r member ih
      change Division.RuleInstance H r at member
      cases member with
      | divide _ _ t k x y hy hov =>
        simpa only [Division.codeEdge, List.map_cons, List.map_nil, replay_const, replay_div] using
          derives_redex (S := S) (.divide t k x y _ (divide_result t k x y hy hov))
      | zero _ _ t k x =>
        simpa only [Division.codeEdge, List.map_cons, List.map_nil, replay_const, replay_div,
          replay_trap] using derives_redex (S := S) (.divTrap t k x 0 .divideByZero (intBinOp_div_zero ..))
      | overflow _ _ t =>
        have overflow : intBinOp t (.div .signed) (BitVec.intMin t.width) (-1) = .error .overflow := by
          cases t <;> rfl
        simpa only [Division.codeEdge, List.map_cons, List.map_nil, replay_const, replay_div,
          replay_trap] using derives_redex (S := S) (.divTrap t .signed _ _ .overflow overflow)
      | nop => exact derives_redex .nop
      | trap _ _ _ _ nonempty admitted => exact replay_bubble nonempty admitted
      | context s f vs before after tail _ tailOk =>
        have middle := ih (Division.codeEdge s f before after) (List.Mem.head _)
        simpa only [Division.codeEdge, List.map_append, replay_values] using
          derives_context (vs.map replayValue) middle (replay_admitted tailOk))

theorem step_readback (P : Profile) (s : Store H) (f : Frame)
    {before : List (AdminInstr I)} {target : Config H} (ok : Admitted S before)
    (step : Step P noHost ⟨s, f, emitCode E.emit before⟩ target) :
    ∃ after, DerivesEdge S before after ∧ target = ⟨s, f, emitCode E.emit after⟩ := by
  obtain ⟨supported, image, source⟩ := emit_properties E ok
  have d := (Division.derives_edge_iff (s := ⟨s, f, emitCode E.emit before⟩) supported).mpr step
  obtain ⟨sameStore, sameFrame⟩ := core_world d
  have translated := replay_derives (S := S) d
  change DerivesEdge S ((emitCode E.emit before).map (replay S)) _ at translated
  rw [source] at translated
  refine ⟨_, translated, ?_⟩
  have targetCode := emit_replay E (core_image E d image)
  rcases target with ⟨store, frame, code⟩
  cases sameStore
  cases sameFrame
  exact congrArg (Config.mk s f) targetCode.symm

theorem steps_readback (P : Profile) (s : Store H) (f : Frame)
    {before : List (AdminInstr I)} {target : Config H} (ok : Admitted S before)
    (path : Steps P noHost ⟨s, f, emitCode E.emit before⟩ target) :
    ∃ after, DerivesPath S before after ∧ target = ⟨s, f, emitCode E.emit after⟩ := by
  induction path with
  | refl => exact ⟨before, .refl, rfl⟩
  | tail _ step ih =>
    obtain ⟨middle, prior, rfl⟩ := ih
    obtain ⟨after, edge, rfl⟩ := step_readback E P s f (path_admitted prior ok) step
    exact ⟨after, prior.tail edge, rfl⟩

end Silmaril.Wasm.Institution.Operational.LegacyDivision.Proofs
