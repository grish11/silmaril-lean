module

public import Silmaril.Wasm.Institution.Operational.Blocks.Native.Defs
public import Silmaril.Wasm.Institution.Operational.Blocks.Thms
public import Silmaril.Wasm.Institution.Operational.Locals.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.Blocks.Rules

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Blocks.Proofs.V1

open Wasm.V1.Execution
open Wasm.Execution.Runtime (AdminInstr Frame ModuleInst Value)

private theorem encode_values (vs : List Value) :
    Locals.v1Codec.encode (Locals.values vs) = values vs := by
  have emit (v : Value) : Locals.v1Codec.emit (.value v) = value v := by
    rcases v with ⟨t, bits⟩
    cases t <;> rfl
  simp [Locals.Codec.encode, Locals.values, values, List.map_map, emit]

private theorem encode_body (ops : List Locals.Op) :
    expression (ops.map Locals.v1Instr) = Locals.v1Codec.encode ops :=
  List.map_map

theorem sound {H : Type} {host : HostSemantics H} (s : Store H) (m : ModuleInst)
    {a b : State} (h : Edge a b) : Step host (v1Config s m a) (v1Config s m b) := by
  rcases invert h with ⟨result, body, rfl, rfl⟩ |
    ⟨result, before, after, rfl, rfl, innerEdge⟩ | ⟨result, ls, vs, rfl, rfl⟩
  · simpa [v1Config, encode_body] using
      (Step.pure (host := host) s ⟨body.locals, m⟩ (PureStep.block result (body.code.map Locals.v1Instr)))
  · exact .label (Locals.v1_sound innerEdge) result.toList.length []
  · simpa [v1Config, encode_values] using
      (Step.pure (host := host) s ⟨ls, m⟩ (PureStep.labelDone result.toList.length [] vs))

private theorem source_nonempty {H : Type} {host : HostSemantics H} {a b : Config H}
    (step : Step host a b) : a.code ≠ [] := by
  induction step with
  | pure s f step =>
    cases step <;> simp [values]
  | context step saved tail ih =>
    intro eq
    exact ih ((List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp eq).1).2)
  | _ => simp

private def wrapper : Admin → Prop
  | .source (.block ..) | .label .. => True
  | _ => False

private inductive WrapperStep {H : Type} (host : HostSemantics H) (s : Store H) (f : Frame) :
    Admin → Config H → Prop where
  | pure {a out} (h : PureStep [a] out) :
      WrapperStep host s f a ⟨s, f, out⟩
  | label {arity cont code target}
      (h : Step host ⟨s, f, code⟩ target) :
      WrapperStep host s f (.label arity cont code)
        ⟨target.store, target.frame, [.label arity cont target.code]⟩

private theorem split_wrapper {H : Type} {host : HostSemantics H} {a b : Config H}
    (step : Step host a b) {op : Admin} (eq : a.code = [op]) (hw : wrapper op) :
    WrapperStep host a.store a.frame op b := by
  induction step with
  | pure s f h => exact .pure (eq ▸ h)
  | label h n cont _ =>
    have same : AdminInstr.label n cont _ = op := List.cons.inj eq |>.1
    subst op
    exact .label h
  | @context s s' f f' before after h saved tail ih =>
    change values saved ++ before ++ tail = [op] at eq
    have length := congrArg List.length eq
    have nonempty : before ≠ [] := source_nonempty h
    have pos := List.length_pos_iff.mpr nonempty
    simp [values] at length
    have hs : saved = [] := List.eq_nil_of_length_eq_zero (by omega)
    have ht : tail = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst saved
    subst tail
    simpa [values] using ih (by simpa [values] using eq)
  | frame | localGet | globalGet | call | memorySize =>
    rw [← (List.cons.inj eq).1] at hw
    exact False.elim hw
  | invokeWasm | invokeHost | invokeHostDiverges =>
    simp [values, List.append_eq_singleton_iff] at eq
    rw [← eq.2] at hw
    exact False.elim hw
  | _ => simp at eq

private theorem pure_block_readback {result : Option NumType}
    {ops : List Locals.Op} {out : List Admin}
    (step : PureStep [.source (.block result (ops.map Locals.v1Instr))] out) :
    out = [.label result.toList.length [] (Locals.v1Codec.encode ops)] := by
  generalize eq : ([.source (.block result (ops.map Locals.v1Instr))] :
    List Admin) = before at step
  cases step <;> simp [values] at eq
  case block bt body =>
    obtain ⟨rfl, rfl⟩ := eq
    rw [encode_body]

private theorem pure_label_readback {result : Option NumType}
    {ops : List Locals.Op} {out : List Admin}
    (step : PureStep [.label result.toList.length [] (Locals.v1Codec.encode ops)] out) :
    ∃ vs, ops = Locals.values vs ∧ out = values vs := by
  have supported := Locals.v1Codec.supports_encode ops
  generalize eq : ([.label result.toList.length [] (Locals.v1Codec.encode ops)] :
    List Admin) = before at step
  cases step <;> simp [values] at eq
  case labelDone n cont vs =>
    have equal : Locals.v1Codec.encode ops = values vs := eq.2.2
    rw [← encode_values] at equal
    exact ⟨vs, by simpa using congrArg Locals.v1Codec.decode equal, rfl⟩
  all_goals
    have body := eq.2.2
    rw [body] at supported
    simp only [Locals.Codec.supports_append, Locals.Codec.supports_cons, Locals.v1Codec,
      Locals.legacyCodec, Locals.legacyRead, Wasm.V1.Instr.toCore, Locals.readInstr,
      Option.isSome_none, Bool.false_eq_true, and_false, false_and] at supported

private theorem no_values_step {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame}
    {vs : List Value} {b : Config H} (step : Step host ⟨s, f, values vs⟩ b) : False := by
  have src : (⟨s, f, values vs⟩ : Config H) =
      Locals.v1Config s f.module ⟨f.locals, Locals.values vs⟩ := by
    cases f
    simp [Locals.v1Config, encode_values]
  rw [src] at step
  obtain ⟨out, edge, _⟩ := Locals.v1_step_iff.mp step
  exact Blocks.Proofs.no_values_edge edge

theorem readback {H : Type} {host : HostSemantics H} {s : Store H} {m : ModuleInst}
    {a : State} {target : Config H} (step : Step host (v1Config s m a) target) :
    ∃ b, Edge a b ∧ target = v1Config s m b := by
  cases a with
  | block result a =>
    have shape := split_wrapper step rfl (by trivial)
    cases shape with
    | pure h => exact ⟨.label result a, enter result a, by rw [pure_block_readback h]; rfl⟩
  | label result a =>
    have shape := split_wrapper step rfl (by trivial)
    cases shape with
    | pure h =>
      obtain ⟨vs, code, rfl⟩ := pure_label_readback h
      have eq : a = ⟨a.locals, Locals.values vs⟩ := by cases a; simp_all
      rw [eq]
      exact ⟨.done a.locals vs, exit result a.locals vs, rfl⟩
    | label h =>
      obtain ⟨out, inner, rfl⟩ := Locals.v1_step_iff.mp h
      exact ⟨.label result out, reduce result inner, rfl⟩
  | done ls vs => exact (no_values_step step).elim

end Silmaril.Wasm.Institution.Operational.Blocks.Proofs.V1
