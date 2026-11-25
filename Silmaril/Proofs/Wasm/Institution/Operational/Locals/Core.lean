module

public import Silmaril.Wasm.Institution.Operational.Locals.Native.Defs
public import Silmaril.Wasm.SingleThreaded.Determinism.HeadDet

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Locals.Proofs

open Silmaril.Semantics.SOS Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Runtime (Value)
open Silmaril.Wasm.SingleThreaded.Det

private theorem core_emit_value (v : Value) :
    coreCodec.emit (.value v) = (LegacyDivision.liftValue v).toAdmin := by
  rcases v with ⟨t, bits⟩
  cases t <;> rfl

@[local simp] private theorem emit_get (i : LocalIdx) :
    coreCodec.emit (.get i) = .plain (.localGet i) := rfl

@[local simp] private theorem emit_set (i : LocalIdx) :
    coreCodec.emit (.set i) = .plain (.localSet i) := rfl

@[local simp] private theorem emit_tee (i : LocalIdx) :
    coreCodec.emit (.tee i) = .plain (.localTee i) := rfl

private theorem core_encode_values (vs : List Value) :
    coreCodec.encode (values vs) = vals (vs.map LegacyDivision.liftValue) := by
  simp [Codec.encode, values, vals, List.map_map, core_emit_value]

private theorem numeric_value {v : Val} (h : (coreCodec.read v.toAdmin).isSome) :
    ∃ w : Value, LegacyDivision.liftValue w = v := by
  cases v with
  | num n => exact ⟨⟨n.type, n.bits⟩, by cases n; rfl⟩
  | vec | ref => contradiction

private theorem numeric_values {vs : List Val} (h : coreCodec.Supported (vals vs)) :
    ∃ ws : List Value, ws.map LegacyDivision.liftValue = vs := by
  induction vs with
  | nil => exact ⟨[], rfl⟩
  | cons v vs ih =>
    obtain ⟨hv, tail⟩ := coreCodec.supports_cons.mp h
    obtain ⟨w, rfl⟩ := numeric_value hv
    obtain ⟨ws, rfl⟩ := ih tail
    exact ⟨w :: ws, rfl⟩

theorem core_sound {H : Type} {P : Profile} (s : Store H) (m : ModuleInst)
    {a b : State} (h : Edge a b) : Step P noHost (coreConfig s m a) (coreConfig s m b) := by
  refine Derives.least (M := fun j => Step P noHost (coreConfig s m j.1) (coreConfig s m j.2)) h ?_
  intro r hr ih
  change RuleInstance r at hr
  cases hr with
  | get ls i v found =>
    have lookup : (Frame.mk (ls.map coreLocal) m).local? i = some (some (LegacyDivision.liftValue v)) := by
      simp [Frame.local?, List.getElem?_map, found, coreLocal]
    simpa [coreConfig, Codec.encode, core_emit_value] using
      (Step.variable (P := P) (host := noHost) (VariableStep.localGet (s := s) lookup))
  | set ls i v bound =>
    have hb : i.toNat < (Frame.mk (ls.map coreLocal) m).locals.length := by simpa using bound
    simpa [coreConfig, Codec.encode, core_emit_value, Frame.setLocal, List.map_set, coreLocal] using
      (Step.variable (P := P) (host := noHost) (VariableStep.localSet (s := s) (v := LegacyDivision.liftValue v) hb))
  | tee ls i v =>
    simpa [coreConfig, Codec.encode, core_emit_value] using
      (Step.variable (P := P) (host := noHost)
        (VariableStep.localTee (s := s) (f := ⟨ls.map coreLocal, m⟩) (x := i)
          (v := LegacyDivision.liftValue v)))
  | context a b saved tail =>
    simpa [coreConfig, core_encode_values] using
      lift_instrs (saved.map LegacyDivision.liftValue) (coreCodec.encode tail) _ _
        (ih (a, b) (List.Mem.head _))

private theorem variable_readback {H : Type} {s : Store H} {f : Frame} {before : List Admin}
    {next : Config H} {ls : List Value} (h : VariableStep ⟨s, f, before⟩ next)
    (locals : f.locals = ls.map coreLocal) (ready : coreCodec.Supported before) :
    ∃ out, Edge ⟨ls, coreCodec.decode before⟩ out ∧ next = coreConfig s f.module out := by
  cases h with
  | @localGet _ _ i v found =>
    simp only [Frame.local?, locals, List.getElem?_map] at found
    cases lookup : ls[i.toNat]? with
    | none => simp [lookup] at found
    | some w =>
      have eq : LegacyDivision.liftValue w = v := by simpa [lookup, coreLocal] using found
      subst v
      refine ⟨⟨ls, [.value w]⟩, fact (.get ls i w lookup), ?_⟩
      cases f
      simp_all [coreConfig, Codec.encode, core_emit_value]
  | @localSet _ _ i v bound =>
    have hb : i.toNat < ls.length := by simpa [locals] using bound
    obtain ⟨w, rfl⟩ := numeric_value (coreCodec.supports_cons.mp ready).1
    have encoded : coreCodec.encode [.value w, .set i] =
        [(LegacyDivision.liftValue w).toAdmin, .plain (.localSet i)] := by
      simp [Codec.encode, core_emit_value]
    rw [← encoded, Codec.decode_encode]
    refine ⟨⟨ls.set i.toNat w, []⟩, fact (.set ls i w hb), ?_⟩
    simp [Frame.setLocal, coreConfig, List.map_set, locals, coreLocal, Codec.encode]
  | @localTee _ _ i v =>
    obtain ⟨w, rfl⟩ := numeric_value (coreCodec.supports_cons.mp ready).1
    have encoded : coreCodec.encode [.value w, .tee i] =
        [(LegacyDivision.liftValue w).toAdmin, .plain (.localTee i)] := by
      simp [Codec.encode, core_emit_value]
    rw [← encoded, Codec.decode_encode]
    refine ⟨⟨ls, [.value w, .value w, .set i]⟩, fact (.tee ls i w), ?_⟩
    cases f
    simp_all [coreConfig, Codec.encode, core_emit_value]
  | globalGet | globalSet =>
    simp only [Codec.supports_cons, coreCodec, readInstr, Option.isSome_none, Bool.false_eq_true,
      and_false, false_and] at ready

private theorem head_readback {H : Type} {P : Profile} {s : Store H} {f : Frame}
    {args : List Val} {op : Admin} {next : Config H} {ls : List Value}
    (h : Head P s f args op next) (locals : f.locals = ls.map coreLocal)
    (ready : coreCodec.Supported (vals args ++ [op])) :
    ∃ out, Edge ⟨ls, coreCodec.decode (vals args ++ [op])⟩ out ∧
      next = coreConfig s f.module out := by
  have allowed := (coreCodec.supports_cons.mp (coreCodec.supports_append.mp ready).2).1
  cases he : coreCodec.read op with
  | none => simp [he] at allowed
  | some ins =>
    have emit := coreCodec.emit_read he
    subst op
    cases ins with
    | value v =>
      have none := h.good.val_none
      simp [core_emit_value] at none
    | get i | set i | tee i =>
      exact variable_readback (h.fam_inv (by change Fam.variable ≠ .control; decide)) locals ready

theorem core_readback {H : Type} {P : Profile} {s : Store H} {m : ModuleInst} {a : State}
    {b : Config H} (step : Step P noHost (coreConfig s m a) b) :
    ∃ out, Edge a out ∧ b = coreConfig s m out := by
  have ready := coreCodec.supports_encode a.code
  rcases Silmaril.Wasm.SingleThreaded.Det.Step.decomp step with head | bubble
  · obtain ⟨saved, args, op, tail, next, eq, hh, rfl⟩ := head
    change coreCodec.encode a.code = _ at eq
    have eq' : coreCodec.encode a.code = vals saved ++ (vals args ++ [op]) ++ tail :=
      by simpa [List.append_assoc] using eq
    rw [eq'] at ready
    obtain ⟨left, tailReady⟩ := coreCodec.supports_append.mp ready
    obtain ⟨savedReady, inner⟩ := coreCodec.supports_append.mp left
    obtain ⟨ws, rfl⟩ := numeric_values savedReady
    obtain ⟨out, edge, rfl⟩ := head_readback hh rfl inner
    refine ⟨⟨out.locals, values ws ++ out.code ++ coreCodec.decode tail⟩, ?_, ?_⟩
    · have code : a.code = values ws ++ coreCodec.decode (vals args ++ [op]) ++ coreCodec.decode tail := by
        rw [← coreCodec.decode_encode a.code, eq', Codec.decode_append, Codec.decode_append,
          ← core_encode_values, Codec.decode_encode]
      have source : a = ⟨a.locals, values ws ++ coreCodec.decode (vals args ++ [op]) ++
          coreCodec.decode tail⟩ := by cases a; simp_all
      rw [source]
      exact Locals.context edge ws (coreCodec.decode tail)
    · simp [coreConfig, core_encode_values, coreCodec.encode_decode tailReady]
  · obtain ⟨saved, discarded, skipped, tail, _, ⟨_, eq, _⟩ | ⟨tag, _, eq, _⟩⟩ := fnv_bubble bubble
    · change coreCodec.encode a.code = _ at eq
      rw [eq] at ready
      have bad := (coreCodec.supports_cons.mp (coreCodec.supports_append.mp ready).2).1
      contradiction
    · change coreCodec.encode a.code = _ at eq
      rw [eq] at ready
      have bad := (coreCodec.supports_cons.mp (coreCodec.supports_append.mp ready).2).1
      contradiction

end Silmaril.Wasm.Institution.Operational.Locals.Proofs
