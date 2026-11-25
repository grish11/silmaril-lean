module

public import Silmaril.Wasm.Institution.Operational.Locals.Native.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Locals.Proofs.Lime1

open Silmaril.Wasm.Lime1.Execution
open Silmaril.Wasm.Execution.Runtime (AdminInstr Value)
open Silmaril.Semantics.SOS

private theorem emit_value (v : Value) : limeCodec.emit (.value v) = value v := by
  rcases v with ⟨t, bits⟩
  cases t <;> rfl

@[local simp] private theorem emit_get (i : LocalIdx) :
    limeCodec.emit (.get i) = .source (.localGet i) := rfl

@[local simp] private theorem emit_set (i : LocalIdx) :
    limeCodec.emit (.set i) = .source (.localSet i) := rfl

@[local simp] private theorem emit_tee (i : LocalIdx) :
    limeCodec.emit (.tee i) = .source (.localTee i) := rfl

private theorem encode_values (vs : List Value) :
    limeCodec.encode (Locals.values vs) = Lime1.Execution.values vs := by
  simp [Codec.encode, Locals.values, Lime1.Execution.values, List.map_map, emit_value]

private theorem decode_values (vs : List Value) :
    limeCodec.decode (Lime1.Execution.values vs) = Locals.values vs := by rw [← encode_values, Codec.decode_encode]

private theorem decode_value (v : Value) :
    limeCodec.decode [value v] = [.value v] := decode_values [v]

private theorem decode_get (i : LocalIdx) :
    limeCodec.decode [.source (.localGet i)] = [.get i] := rfl

private theorem decode_set (i : LocalIdx) :
    limeCodec.decode [.source (.localSet i)] = [.set i] := rfl

private theorem decode_tee (i : LocalIdx) :
    limeCodec.decode [.source (.localTee i)] = [.tee i] := rfl

theorem sound {H : Type} {host : HostSemantics H} (s : Store H)
    (m : Silmaril.Wasm.Execution.Runtime.ModuleInst) {a b : State} (h : Edge a b) :
    Step host (limeConfig s m a) (limeConfig s m b) := by
  refine Derives.least (M := fun j => Step host (limeConfig s m j.1) (limeConfig s m j.2)) h ?_
  intro r hr ih
  change RuleInstance r at hr
  cases hr with
  | get ls i v found =>
    simpa [limeConfig, Codec.encode, emit_value] using (Step.localGet (host := host) s ⟨ls, m⟩ i v found)
  | set ls i v bound =>
    simpa [limeConfig, Codec.encode, emit_value] using
      (Step.localSet (host := host) s ⟨ls, m⟩ i v _ (List.getElem?_eq_getElem bound))
  | tee ls i v =>
    simpa [limeConfig, Codec.encode, emit_value] using (Step.pure (host := host) s ⟨ls, m⟩ (PureStep.localTee i v))
  | context a b saved tail =>
    simpa [limeConfig, encode_values] using
      Step.context (ih (a, b) (List.Mem.head _)) saved (limeCodec.encode tail)

private theorem pure_readback {types : List Silmaril.Wasm.Lime1.FuncType} {before after : List Admin} {ls : List Value}
    (h : PureStep types before after) (ready : limeCodec.Supported before) :
    ∃ out, Edge ⟨ls, limeCodec.decode before⟩ ⟨ls, out⟩ ∧ limeCodec.encode out = after := by
  cases h with
  | localTee i v =>
    refine ⟨[.value v, .value v, .set i], ?_, by simp [Codec.encode, emit_value]⟩
    change Edge ⟨ls, limeCodec.decode ([value v] ++ [.source (.localTee i)])⟩ _
    rw [Codec.decode_append, decode_value, decode_tee]
    exact fact (.tee ls i v)
  | _ =>
    simp only [Codec.supports_append, Codec.supports_cons, limeCodec, legacyCodec, legacyRead,
      Silmaril.Wasm.Lime1.Instr.toCore, readInstr, Option.isSome_none, Bool.false_eq_true, and_false,
      false_and] at ready

theorem readback {H : Type} {host : HostSemantics H} {a b : Config H}
    (h : Step host a b) (ready : limeCodec.Supported a.code) :
    ∃ out, Edge ⟨a.frame.locals, limeCodec.decode a.code⟩ out ∧
      b = limeConfig a.store a.frame.module out := by
  induction h with
  | pure s f step =>
    obtain ⟨out, edge, rendered⟩ := pure_readback (ls := f.locals) step ready
    exact ⟨⟨f.locals, out⟩, edge, by cases f; simp [limeConfig, rendered]⟩
  | localGet s f i v found =>
    rw [show limeCodec.decode [AdminInstr.source (.localGet i)] = [.get i] from decode_get i]
    exact ⟨⟨f.locals, [.value v]⟩, fact (.get _ i v found), by cases f; simp [limeConfig, Codec.encode, emit_value]⟩
  | localSet s f i v old found =>
    change ∃ out, Edge ⟨f.locals, limeCodec.decode ([value v] ++ [.source (.localSet i)])⟩ out ∧ _
    rw [Codec.decode_append, decode_value, decode_set]
    exact ⟨⟨f.locals.set i.toNat v, []⟩, fact (.set _ i v (List.getElem?_eq_some_iff.mp found).1), rfl⟩
  | @context s s' f f' before after step saved tail ih =>
    obtain ⟨left, tailReady⟩ := limeCodec.supports_append.mp ready
    have middle := (limeCodec.supports_append.mp left).2
    obtain ⟨out, edge, eq⟩ := ih middle
    refine ⟨⟨out.locals, Locals.values saved ++ out.code ++ limeCodec.decode tail⟩, ?_, ?_⟩
    · simpa [decode_values] using Locals.context edge saved (limeCodec.decode tail)
    · cases eq
      simp [limeConfig, encode_values, limeCodec.encode_decode tailReady]
  | _ =>
    simp only [Codec.supports_append, Codec.supports_cons, limeCodec, legacyCodec, legacyRead,
      Silmaril.Wasm.Lime1.Instr.toCore, readInstr, Option.isSome_none, Bool.false_eq_true, and_false,
      false_and] at ready

end Silmaril.Wasm.Institution.Operational.Locals.Proofs.Lime1
