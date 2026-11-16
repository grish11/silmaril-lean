module

public import Silmaril.Wasm.Cfg.MachineClosed.Thms
public import Silmaril.Wasm.Abstract.SelfLoop.Thms

@[expose] public section

/-!
# `(func (call 0))` in the block-CFG machine: proofs

The body `[call x]` of a self-call is one basic block with no terminator. Its only machine
steps go to a sink, whatever the oracle, so the machine has no infinite run; the block's body
reaches the self-call, which `closedDiv` names (no closed-oracle entry, from Core divergence of
the invocation), so `MDivC` holds at the CFG entry.
-/

namespace Silmaril.Wasm.Cfg.Proofs.ExampleRec

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Abstract

variable {H : Type}

theorem segment_call (x : FuncIdx) : segment [Instr.call x] = [⟨[.call x], none⟩] := by
  simp [segment, segmentAux, isTerminator]

theorem lookup_call (x : FuncIdx) (b : BlockId) :
    lookup [Instr.call x] b = if b = ⟨[], 0⟩ then some ⟨[.call x], none⟩ else none := by
  obtain ⟨q, i⟩ := b
  rw [Machine.lookup_eq]
  cases q with
  | nil =>
    simp only [Machine.seqAt, Option.bind_some, segment_call]
    cases i with
    | zero => simp
    | succ i => simp
  | cons st q =>
    obtain ⟨m, a⟩ := st
    simp only [Machine.seqAt, segment_call]
    cases m with
    | zero => simp [armOf]
    | succ m => simp

theorem lookup_entry (x : FuncIdx) :
    lookup [Instr.call x] ⟨[], 0⟩ = some ⟨[.call x], none⟩ := by
  simp [lookup_call]

theorem initial_call (x : FuncIdx) (s : Store H) (f : Frame) :
    initial [Instr.call x] s f = ⟨.block ⟨[], 0⟩, [], [], s, f⟩ := by
  simp [initial, cfgEntry, entry, lookup_call]

/-- **Every machine step from the entry of `[call x]` goes to a sink**, for every oracle. -/
theorem step_sink {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H} (x : FuncIdx)
    {s : Store H} {f : Frame} {st : MState H}
    (h : MStepC P host C [Instr.call x] (initial [Instr.call x] s f) st) : st.node.IsSink := by
  rw [initial_call] at h
  cases h with
  | fall hb ht hr =>
    simp only [lookup_entry, Option.some.injEq] at hb; subst hb
    simp [goto, entry, lookup_call, cont, contRev, Target.IsSink]
  | bodyTrap => simp [Target.IsSink]
  | bodyRaise => simp [Target.IsSink]
  | bodyCatch _ _ _ hL => simp at hL
  | br hb ht => simp only [lookup_entry, Option.some.injEq] at hb; subst hb; cases ht
  | brIfTaken hb ht => simp only [lookup_entry, Option.some.injEq] at hb; subst hb; cases ht
  | brIfNot hb ht => simp only [lookup_entry, Option.some.injEq] at hb; subst hb; cases ht
  | brDataTaken hb ht => simp only [lookup_entry, Option.some.injEq] at hb; subst hb; cases ht
  | brDataNot hb ht => simp only [lookup_entry, Option.some.injEq] at hb; subst hb; cases ht
  | enter hb ht => simp only [lookup_entry, Option.some.injEq] at hb; subst hb; cases ht
  | ret hb ht => simp only [lookup_entry, Option.some.injEq] at hb; subst hb; cases ht
  | brOut => simp [Target.IsSink]
  | brIfOut => simp [Target.IsSink]
  | brDataOut => simp [Target.IsSink]
  | trap hb ht => simp only [lookup_entry, Option.some.injEq] at hb; subst hb; cases ht
  | termTrap hb ht => simp only [lookup_entry, Option.some.injEq] at hb; subst hb; cases ht
  | raise hb ht => simp only [lookup_entry, Option.some.injEq] at hb; subst hb; cases ht
  | catch_ hb ht => simp only [lookup_entry, Option.some.injEq] at hb; subst hb; cases ht
  | tailNull hb ht => simp only [lookup_entry, Option.some.injEq] at hb; subst hb; cases ht
  | tail hb ht => simp only [lookup_entry, Option.some.injEq] at hb; subst hb; cases ht

/-- **The machine has no infinite run from the entry of `[call x]`**, for every oracle. -/
theorem not_infinite {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H}
    (x : FuncIdx) (s : Store H) (f : Frame) :
    ¬ InfiniteTrace (MStepC P host C [Instr.call x]) (initial [Instr.call x] s f) := by
  intro h
  obtain ⟨st, hs, h'⟩ := h.unfold
  obtain ⟨st₁, hs₁, -⟩ := h'.unfold
  obtain ⟨b, hb⟩ : ∃ b, st.node = .block b := by cases hs₁ <;> exact ⟨_, rfl⟩
  have := step_sink x hs
  rw [hb] at this
  exact this

theorem rec_diverges (P : Profile) : Diverges P Binaryen.closedHost (invoke recStore 0 []) := by
  have hm : _ ∈ wasmFun P Binaryen.closedHost 0 recStore [] :=
    (rec_wasmFun P).symm ▸ Set.mem_singleton _
  rcases hm with ⟨c', r, -, -, he⟩ | ⟨-, hd⟩
  · cases r <;> simp [endOfResult] at he
  · exact hd

theorem rec_closedDiv (P : Profile) : closedDiv recStore 0 [] :=
  ⟨⟨recStore_ok, recStore_nativeFuncsOk, recStore_storeChk, rec_invokeOk⟩,
    (closedCall_none_iff_diverges recStore_ok recStore_nativeFuncsOk recStore_storeChk
      rec_invokeOk P).2 (rec_diverges P)⟩

/-- **`MDivC` at the entry of the self-call**: its block's body reaches `call x`, resolving to
the function itself, which `closedDiv` names. -/
theorem rec_mdivC (P : Profile) {fi : FuncInst Empty} {x : FuncIdx} {f : Frame}
    (hfi : recStore.funcs[0]? = some fi) (hx : f.module.funcs[x.toNat]? = some 0) :
    MDivC P (fun _ _ _ _ => False) Abstract.closedCallOk closedDiv [Instr.call x]
      (initial [Instr.call x] recStore f) := by
  have hty : Validation.DefType.funcType? fi.type = some ([], []) := by
    simpa [hfi] using recStore_funcType
  refine .inr ⟨_, .refl, ⟨[], 0⟩, ⟨[.call x], none⟩, [], [], x, recStore, f, [], [], 0, fi, [], [],
    by rw [initial_call], by simp [lookup_call], rfl, by rw [initial_call]; exact .nil,
    by simp [Store.func?, hx, hfi], hty, rfl, rec_closedDiv P⟩

end Silmaril.Wasm.Cfg.Proofs.ExampleRec
