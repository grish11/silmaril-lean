module

public import Silmaril.Wasm.Cfg.ExampleRef.Defs
public import Silmaril.Wasm.Cfg.MachineClosed.Thms
public import Silmaril.Wasm.Abstract.SelfLoop.Thms
public import Silmaril.Proofs.Wasm.Cfg.ExampleRec
public import Silmaril.Proofs.Wasm.Cfg.RegionDivC

@[expose] public section

/-!
# Calls by reference in the block-CFG machine: proofs

Each body is one basic block with no terminator. `refBody` reaches `call_ref` of the function `x` names,
which in `recStore` is the self-call of `recMod` and which `closedDiv` names, so `MDivC` holds
through `BodyCallDivRef`; every machine step from the entry goes to a sink, so there is no
infinite machine run. `nullBody` steps in Core to `ref.null; call_ref`, which traps.
-/

namespace Silmaril.Wasm.Cfg.Proofs.ExampleRef

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Abstract
  Silmaril.Wasm.Cfg.ExampleRef

variable {H : Type}

/-- A two-instruction body without terminator. -/
abbrev two (i j : Instr) : List Instr := [i, j]

theorem segment_two {i j : Instr} (hi : isTerminator i = false) (hj : isTerminator j = false) :
    segment (two i j) = [⟨[i, j], none⟩] := by
  simp [segment, segmentAux, hi, hj]

theorem lookup_two {i j : Instr} (hi : isTerminator i = false) (hj : isTerminator j = false)
    (b : BlockId) :
    lookup (two i j) b = if b = ⟨[], 0⟩ then some ⟨[i, j], none⟩ else none := by
  obtain ⟨q, k⟩ := b
  rw [Machine.lookup_eq]
  cases q with
  | nil =>
    simp only [Machine.seqAt, Option.bind_some, segment_two hi hj]
    cases k with
    | zero => simp
    | succ k => simp
  | cons st q =>
    obtain ⟨m, a⟩ := st
    simp only [Machine.seqAt, segment_two hi hj]
    cases m with
    | zero => simp [armOf]
    | succ m => simp

theorem initial_two {i j : Instr} (hi : isTerminator i = false) (hj : isTerminator j = false)
    (s : Store H) (f : Frame) :
    initial (two i j) s f = ⟨.block ⟨[], 0⟩, [], [], s, f⟩ := by
  simp [initial, cfgEntry, entry, lookup_two hi hj]

/-- **Every machine step from the entry of a two-instruction body without terminator goes to a
sink**, for every oracle. -/
theorem step_sink {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H} {i j : Instr}
    (hi : isTerminator i = false) (hj : isTerminator j = false) {s : Store H} {f : Frame}
    {st : MState H} (h : MStepC P host C (two i j) (initial (two i j) s f) st) : st.node.IsSink := by
  rw [initial_two hi hj] at h
  have hl := lookup_two hi hj (b := ⟨[], 0⟩)
  simp only [↓reduceIte] at hl
  cases h with
  | fall hb ht hr =>
    rw [hl, Option.some.injEq] at hb; subst hb
    simp [goto, entry, lookup_two hi hj, cont, contRev, Target.IsSink]
  | bodyTrap => simp [Target.IsSink]
  | bodyRaise => simp [Target.IsSink]
  | bodyCatch _ _ _ hL => simp at hL
  | brOut => simp [Target.IsSink]
  | catchOut => simp [Target.IsSink]
  | bodyCatchOut => simp [Target.IsSink]
  | brIfOut => simp [Target.IsSink]
  | brDataOut => simp [Target.IsSink]
  | br hb ht => rw [hl, Option.some.injEq] at hb; subst hb; cases ht
  | brIfTaken hb ht => rw [hl, Option.some.injEq] at hb; subst hb; cases ht
  | brIfNot hb ht => rw [hl, Option.some.injEq] at hb; subst hb; cases ht
  | brDataTaken hb ht => rw [hl, Option.some.injEq] at hb; subst hb; cases ht
  | brDataNot hb ht => rw [hl, Option.some.injEq] at hb; subst hb; cases ht
  | enter hb ht => rw [hl, Option.some.injEq] at hb; subst hb; cases ht
  | ret hb ht => rw [hl, Option.some.injEq] at hb; subst hb; cases ht
  | trap hb ht => rw [hl, Option.some.injEq] at hb; subst hb; cases ht
  | termTrap hb ht => rw [hl, Option.some.injEq] at hb; subst hb; cases ht
  | raise hb ht => rw [hl, Option.some.injEq] at hb; subst hb; cases ht
  | catch_ hb ht => rw [hl, Option.some.injEq] at hb; subst hb; cases ht
  | tailNull hb ht => rw [hl, Option.some.injEq] at hb; subst hb; cases ht
  | tail hb ht => rw [hl, Option.some.injEq] at hb; subst hb; cases ht

/-- **No infinite machine run from the entry of a two-instruction body without terminator**,
for every oracle. -/
theorem not_infinite {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H} {i j : Instr}
    (hi : isTerminator i = false) (hj : isTerminator j = false) (s : Store H) (f : Frame) :
    ¬ InfiniteTrace (MStepC P host C (two i j)) (initial (two i j) s f) := by
  intro h
  obtain ⟨st, hs, h'⟩ := h.unfold
  obtain ⟨st₁, hs₁, -⟩ := h'.unfold
  obtain ⟨b, hb⟩ : ∃ b, st.node = .block b := by cases hs₁ <;> exact ⟨_, rfl⟩
  have := step_sink hi hj hs
  rw [hb] at this
  exact this

theorem refBody_two (x : FuncIdx) (y : TypeIdx) : refBody x y = two (.refFunc x) (.callRef y) := rfl

theorem nullBody_two (ht : HeapType) (y : TypeIdx) :
    nullBody ht y = two (.refNull ht) (.callRef y) := rfl

/-- **`MDivC` at the entry of `refBody`**: its block's body runs `ref.func 0` and reaches
`call_ref` of function `0` of `recStore`, which `closedDiv` names (`BodyCallDivRef`). -/
theorem ref_mdivC (P : Profile) {fi : FuncInst Empty} {f : Frame} (x : FuncIdx) (y : TypeIdx)
    (hfi : recStore.funcs[0]? = some fi) (hx : f.module.funcs[x.toNat]? = some 0) :
    MDivC P (fun _ _ _ _ => False) Abstract.closedCallOk closedDiv (refBody x y)
      (initial (refBody x y) recStore f) := by
  have hty : Validation.DefType.funcType? fi.type = some ([], []) := by
    simpa [hfi] using recStore_funcType
  have hpre : RunC P (fun _ _ _ _ => False) Abstract.closedCallOk recStore f []
      (expression [.refFunc x]) recStore f (.normal [.ref (.func 0)]) := by
    have hs : Steps P (fun _ _ _ _ => False) ⟨recStore, f, vals [] ++ [.plain (.refFunc x)]⟩
        ⟨recStore, f, vals [.ref (.func 0)]⟩ :=
      .single (by simpa [vals, Val.toAdmin] using
        (Step.reference (P := P) (host := fun _ _ _ _ => False)
          (RefStep.refFunc (s := recStore) (f := f) (x := x) hx)))
    exact .simple (by simp [SingleThreaded.Det.famOf]) hs .nil
  rw [refBody_two, initial_two (by simp [isTerminator]) (by simp [isTerminator])]
  refine .inr ⟨_, .refl, .inr (.inr ⟨⟨[], 0⟩, ⟨[.refFunc x, .callRef y], none⟩, [.refFunc x],
    [], y, recStore, f, [], [], 0, fi, [], [], rfl, ?_, rfl, hpre, hfi, hty, rfl,
    ExampleRec.rec_closedDiv P⟩)⟩
  simp [lookup_two (i := .refFunc x) (j := .callRef y) (by simp [isTerminator])
    (by simp [isTerminator])]

/-- **`nullBody` never diverges in Core** (every profile and host): `ref.null` steps to the null
reference, and `call_ref` of null traps. -/
theorem null_not_div {P : Profile} {host : HostSemantics H} (ht : HeapType) (y : TypeIdx)
    (s : Store H) (f : Frame) : ¬ Diverges P host ⟨s, f, expression (nullBody ht y)⟩ := by
  intro hd
  obtain ⟨c₁, hs, hd₁⟩ := hd.unfold
  have hs' : Step P host ⟨s, f, vals [] ++ .plain (.refNull ht) :: [.plain (.callRef y)]⟩ c₁ := by
    simpa [nullBody, expression, vals] using hs
  obtain ⟨ws, us, c₀, hvs, hf, rfl⟩ := Proofs.Region.noncontrol_head
    (by simp [SingleThreaded.Det.famOf]) hs'
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 hvs.symm
  have hc₀ : c₀ = ⟨s, f, [.ref .null]⟩ := by
    generalize hc : (⟨s, f, vals [] ++ [.plain (.refNull ht)]⟩ : Config H) = c at hf
    cases hf with
    | reference h =>
      cases h <;> simp only [Config.mk.injEq] at hc <;>
        first
          | (have h2 := congrArg List.getLast? hc.2.2; simp at h2; done)
          | (obtain ⟨rfl, rfl, -⟩ := hc; rfl)
    | _ =>
      rename_i h
      cases h <;>
      (simp only [Config.mk.injEq] at hc
       have h2 := congrArg List.getLast? hc.2.2
       simp at h2)
  subst hc₀
  obtain ⟨c₂, hs₂, hd₂⟩ := hd₁.unfold
  have hs₂' : Step P host ⟨s, f, vals [.ref .null] ++ .plain (.callRef y) :: []⟩ c₂ := by
    simpa [vals, Val.toAdmin] using hs₂
  rcases Step.callRef_top_inv_seq (r := .plain (.callRef y)) trivial hs₂' with
    ⟨w, hw, rfl⟩ | ⟨w, a, fi, hw, -⟩
  · have hl := congrArg List.length hw
    simp at hl
    subst hl
    exact Proofs.Region.trapForm_not_div ⟨[], [], by simp⟩ hd₂
  · have := congrArg List.getLast? hw; simp at this

/-- **The machine at `nullBody` traps**: its block's body runs to a trap, and the machine moves
to the `trap` sink in the same store and frame (every profile, host and oracle). -/
theorem null_trap {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H} (ht : HeapType)
    (y : TypeIdx) (s : Store H) (f : Frame) :
    MStepC P host C (nullBody ht y) (initial (nullBody ht y) s f) ⟨.trap, [], [], s, f⟩ := by
  rw [nullBody_two, initial_two (by simp [isTerminator]) (by simp [isTerminator])]
  have hl := lookup_two (i := .refNull ht) (j := .callRef y) (by simp [isTerminator])
    (by simp [isTerminator]) ⟨[], 0⟩
  simp only [↓reduceIte] at hl
  refine .bodyTrap hl ?_
  have hs : Steps P host ⟨s, f, vals [] ++ [.plain (.refNull ht)]⟩ ⟨s, f, vals [.ref .null]⟩ :=
    .single (by simpa [vals, Val.toAdmin] using
      (Step.reference (P := P) (host := host) (RefStep.refNull (s := s) (f := f) ht)))
  exact .simple (by simp [SingleThreaded.Det.famOf]) hs
    (by simpa using (RunC.callRefNull (P := P) (host := host) (C := C) (s := s) (f := f) (ws := [])
      (y := y) (code := [])))

end Silmaril.Wasm.Cfg.Proofs.ExampleRef
