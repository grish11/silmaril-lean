module

public import Silmaril.Wasm.Institution.Operational.Locals.Native.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Locals.Proofs.V1

open Silmaril.Wasm.V1.Execution
open Silmaril.Wasm.Execution.Runtime (AdminInstr Value)
open Silmaril.Semantics.SOS

private theorem emit_value (v : Value) : v1Codec.emit (.value v) = value v := by
  rcases v with ⟨t, bits⟩
  cases t <;> rfl

@[local simp] private theorem emit_get (i : LocalIdx) :
    v1Codec.emit (.get i) = .source (.localGet i) := rfl

@[local simp] private theorem emit_set (i : LocalIdx) :
    v1Codec.emit (.set i) = .source (.localSet i) := rfl

@[local simp] private theorem emit_tee (i : LocalIdx) :
    v1Codec.emit (.tee i) = .source (.localTee i) := rfl

private theorem encode_values (vs : List Value) :
    v1Codec.encode (Locals.values vs) = V1.Execution.values vs := by
  simp [Codec.encode, Locals.values, V1.Execution.values, List.map_map, emit_value]

private theorem decode_values (vs : List Value) :
    v1Codec.decode (V1.Execution.values vs) = Locals.values vs := by rw [← encode_values, Codec.decode_encode]

private theorem decode_value (v : Value) :
    v1Codec.decode [value v] = [.value v] := decode_values [v]

private theorem decode_get (i : LocalIdx) :
    v1Codec.decode [.source (.localGet i)] = [.get i] := rfl

private theorem decode_set (i : LocalIdx) :
    v1Codec.decode [.source (.localSet i)] = [.set i] := rfl

private theorem decode_tee (i : LocalIdx) :
    v1Codec.decode [.source (.localTee i)] = [.tee i] := rfl

theorem sound {H : Type} {host : HostSemantics H} (s : Store H)
    (m : Silmaril.Wasm.Execution.Runtime.ModuleInst) {a b : State} (h : Edge a b) :
    Step host (v1Config s m a) (v1Config s m b) := by
  refine Derives.least (M := fun j => Step host (v1Config s m j.1) (v1Config s m j.2)) h ?_
  intro r hr ih
  change RuleInstance r at hr
  cases hr with
  | get ls i v found =>
    simpa [v1Config, Codec.encode, emit_value] using (Step.localGet (host := host) s ⟨ls, m⟩ i v found)
  | set ls i v bound =>
    simpa [v1Config, Codec.encode, emit_value] using
      (Step.localSet (host := host) s ⟨ls, m⟩ i v _ (List.getElem?_eq_getElem bound))
  | tee ls i v =>
    simpa [v1Config, Codec.encode, emit_value] using (Step.pure (host := host) s ⟨ls, m⟩ (PureStep.localTee i v))
  | context a b saved tail =>
    simpa [v1Config, encode_values] using
      Step.context (ih (a, b) (List.Mem.head _)) saved (v1Codec.encode tail)

private theorem pure_readback {before after : List Admin} {ls : List Value}
    (h : PureStep before after) (ready : v1Codec.Supported before) :
    ∃ out, Edge ⟨ls, v1Codec.decode before⟩ ⟨ls, out⟩ ∧ v1Codec.encode out = after := by
  cases h with
  | localTee i v =>
    refine ⟨[.value v, .value v, .set i], ?_, by simp [Codec.encode, emit_value]⟩
    change Edge ⟨ls, v1Codec.decode ([value v] ++ [.source (.localTee i)])⟩ _
    rw [Codec.decode_append, decode_value, decode_tee]
    exact fact (.tee ls i v)
  | _ =>
    simp only [Codec.supports_append, Codec.supports_cons, v1Codec, legacyCodec, legacyRead,
      Silmaril.Wasm.V1.Instr.toCore, readInstr, Option.isSome_none, Bool.false_eq_true, and_false,
      false_and] at ready

theorem readback {H : Type} {host : HostSemantics H} {a b : Config H}
    (h : Step host a b) (ready : v1Codec.Supported a.code) :
    ∃ out, Edge ⟨a.frame.locals, v1Codec.decode a.code⟩ out ∧
      b = v1Config a.store a.frame.module out := by
  induction h with
  | pure s f step =>
    obtain ⟨out, edge, rendered⟩ := pure_readback (ls := f.locals) step ready
    exact ⟨⟨f.locals, out⟩, edge, by cases f; simp [v1Config, rendered]⟩
  | localGet s f i v found =>
    rw [show v1Codec.decode [AdminInstr.source (.localGet i)] = [.get i] from decode_get i]
    exact ⟨⟨f.locals, [.value v]⟩, fact (.get _ i v found), by cases f; simp [v1Config, Codec.encode, emit_value]⟩
  | localSet s f i v old found =>
    change ∃ out, Edge ⟨f.locals, v1Codec.decode ([value v] ++ [.source (.localSet i)])⟩ out ∧ _
    rw [Codec.decode_append, decode_value, decode_set]
    exact ⟨⟨f.locals.set i.toNat v, []⟩, fact (.set _ i v (List.getElem?_eq_some_iff.mp found).1), rfl⟩
  | @context s s' f f' before after step saved tail ih =>
    obtain ⟨left, tailReady⟩ := v1Codec.supports_append.mp ready
    have middle := (v1Codec.supports_append.mp left).2
    obtain ⟨out, edge, eq⟩ := ih middle
    refine ⟨⟨out.locals, Locals.values saved ++ out.code ++ v1Codec.decode tail⟩, ?_, ?_⟩
    · simpa [decode_values] using Locals.context edge saved (v1Codec.decode tail)
    · cases eq
      simp [v1Config, encode_values, v1Codec.encode_decode tailReady]
  | _ =>
    simp only [Codec.supports_append, Codec.supports_cons, v1Codec, legacyCodec, legacyRead,
      Silmaril.Wasm.V1.Instr.toCore, readInstr, Option.isSome_none, Bool.false_eq_true, and_false,
      false_and] at ready

end Silmaril.Wasm.Institution.Operational.Locals.Proofs.V1
