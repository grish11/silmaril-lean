module

public import Silmaril.Wasm.Cfg.Machine.Defs
public import Silmaril.Wasm.Cfg.Block.Thms
public import Silmaril.Proofs.Wasm.Cfg.Region

@[expose] public section

namespace Silmaril.Wasm.Cfg.Proofs.Machine

set_option linter.unusedSimpArgs false

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics

set_option linter.unusedSimpArgs false

variable {H : Type} {P : Profile} {host : HostSemantics H}

@[simp] theorem goto_node (t : Target) (d : Nat) (ls : List LFrame) (stk : List Val) (s : Store H)
    (f : Frame) : (goto t d ls stk s f).node = t := rfl

theorem mstep_edge {body : Expr} {st st' : MState H} (h : MStep P host body st st') {b : BlockId}
    (hn : st.node = .block b) : Edge body b st'.node ∨ st'.node = .trap := by
  cases h with
  | fall hb ht => left; cases hn; exact ⟨_, hb, by simp [succOf, ht]⟩
  | br hb ht =>
    left; cases hn; refine ⟨_, hb, ?_⟩
    split <;> simp [succOf, ht]
  | brIfTaken hb ht =>
    left; cases hn; refine ⟨_, hb, ?_⟩
    split <;> simp [succOf, ht]
  | brIfNot hb ht => left; cases hn; exact ⟨_, hb, by simp [succOf, ht]⟩
  | @enter _ sg _ _ _ _ _ _ _ _ _ i a c bt _ _ _ _ _ hb ht harm hkind =>
    left; cases hn; refine ⟨_, hb, ?_⟩
    cases hkind <;> rcases a with _ | _ | a <;> simp_all [armOf, succOf]
  | ret hb ht => left; cases hn; exact ⟨_, hb, by simp [succOf, ht]⟩
  | trap hb ht => left; cases hn; exact ⟨_, hb, by simp [succOf, ht]⟩
  | bodyTrap => right; rfl
  | raise hb ht hi =>
    left; cases hn; refine ⟨_, hb, ?_⟩
    rename_i i _
    cases i <;> simp_all [Instr.IsThrow, succOf]

end Silmaril.Wasm.Cfg.Proofs.Machine

namespace Silmaril.Wasm.Cfg.Proofs.Machine

set_option linter.unusedSimpArgs false

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem mstep_from_block {body : Expr} {st st' : MState H} (h : MStep P host body st st') :
    ∃ b, st.node = .block b := by
  cases h <;> exact ⟨_, rfl⟩

end Silmaril.Wasm.Cfg.Proofs.Machine

namespace Silmaril.Wasm.Cfg.Proofs.Machine

set_option linter.unusedSimpArgs false

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics

theorem blockAt_eq : ∀ (q : List SeqStep) (is : List Instr) (j : Nat),
    blockAt (segment is) 0 q j = (seqAt is q).bind fun c => (segment c)[j]?
  | [], is, j => by simp [blockAt, seqAt]
  | (m, a) :: q, is, j => by
    simp only [blockAt, Nat.zero_le, ↓reduceIte, Nat.sub_zero, seqAt]
    cases h1 : (segment is)[m]? with
    | none => simp
    | some s =>
      cases h2 : s.term with
      | none => simp [h2]
      | some t =>
        cases h3 : armOf t a with
        | none => simp [h2, h3]
        | some c => simp [h2, h3, blockAt_eq q c j]

/-- **The block a `BlockId` names** is block `idx` of the sequence at its path. -/
theorem lookup_eq (body : Expr) (b : BlockId) :
    lookup body b = (seqAt body b.seq).bind fun c => (segment c)[b.idx]? :=
  blockAt_eq b.seq body b.idx

/-- What is left of a sequence from block `i` is that block, then what is left from `i + 1`. -/
theorem restAt_cons {c : List Instr} {i : Nat} {sg : Segment} (h : (segment c)[i]? = some sg) :
    restAt c i = sg.instrs ++ restAt c (i + 1) := by
  have hi : i < (segment c).length := by
    rcases Nat.lt_or_ge i (segment c).length with h' | h'
    · exact h'
    · simp [List.getElem?_eq_none h'] at h
  unfold restAt
  rw [List.drop_eq_getElem_cons hi]
  simp [List.getElem?_eq_getElem hi] at h
  simp [h]

theorem restAt_zero (c : List Instr) : restAt c 0 = c := by
  simpa [restAt] using (segment_isSegmentation c).1

theorem restAt_end {c : List Instr} {i : Nat} (h : (segment c)[i]? = none) : restAt c i = [] := by
  unfold restAt
  rw [List.drop_eq_nil_of_le (by simpa [List.getElem?_eq_none_iff] using h)]
  rfl

end Silmaril.Wasm.Cfg.Proofs.Machine

namespace Silmaril.Wasm.Cfg.Proofs.Machine

set_option linter.unusedSimpArgs false

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem seg_of_lookup {body : Expr} {b : BlockId} {sg : Segment} (hb : lookup body b = some sg) :
    ∃ c, seqAt body b.seq = some c ∧ (segment c)[b.idx]? = some sg := by
  rw [lookup_eq] at hb
  cases hc : seqAt body b.seq with
  | none => simp [hc] at hb
  | some c => exact ⟨c, rfl, by simpa [hc] using hb⟩

/-- **The sequence layer of a fall-through step is sound for `Region.Run`**: falling out of
block `i` (no terminator) after its body ran, then running the rest of the sequence from block
`i + 1`, is a run of the rest from block `i`. -/
theorem fall_sound {c : List Instr} {i : Nat} {sg : Segment} (hsg : (segment c)[i]? = some sg)
    (ht : sg.term = none) {s s₁ s' : Store H} {f f₁ f' : Frame} {stk stk₁ : List Val} {o : Out}
    (hr : Run P host s f stk (expression sg.body) s₁ f₁ (.normal stk₁))
    (hk : Run P host s₁ f₁ stk₁ (expression (restAt c (i + 1))) s' f' o) :
    Run P host s f stk (expression (restAt c i)) s' f' o := by
  rw [restAt_cons hsg]
  have e : sg.instrs = sg.body := by simp [Segment.instrs, ht]
  rw [e]
  simpa [expression] using Proofs.Region.run_append hr hk

/-- And conversely: a run of the rest of a sequence from a block with no terminator runs the
block's body to values, then the rest from the next block, or ends inside the body. -/
theorem fall_complete {c : List Instr} {i : Nat} {sg : Segment} (hsg : (segment c)[i]? = some sg)
    (ht : sg.term = none) {s s' : Store H} {f f' : Frame} {stk : List Val} {o : Out}
    (h : Run P host s f stk (expression (restAt c i)) s' f' o) :
    ∃ s₁ f₁ o₁, Run P host s f stk (expression sg.body) s₁ f₁ o₁ ∧
      Then P host s₁ f₁ o₁ (expression (restAt c (i + 1))) s' f' o := by
  rw [restAt_cons hsg] at h
  have e : sg.instrs = sg.body := by simp [Segment.instrs, ht]
  rw [e] at h
  exact Proofs.Region.run_split h (by simp [expression])

end Silmaril.Wasm.Cfg.Proofs.Machine

namespace Silmaril.Wasm.Cfg.Proofs.Machine

set_option linter.unusedSimpArgs false

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **Context lifting through the label invariant**: if every region run of `inner'` (from
`s₁, f₁`) is a run of `inner` (from `s, f`), the same holds for their code under the same
label frames. -/
theorem wrap_mono {body : Expr} {s s₁ : Store H} {f f₁ : Frame} :
    ∀ (rp : List SeqStep) (ls : List LFrame) {inner inner' X X' : List Admin},
      wrap body rp ls inner = some X → wrap body rp ls inner' = some X' →
      (∀ {o : Out} {s₂ : Store H} {f₂ : Frame},
        Run P host s₁ f₁ [] inner' s₂ f₂ o → Run P host s f [] inner s₂ f₂ o) →
      ∀ {o : Out} {s₂ : Store H} {f₂ : Frame},
        Run P host s₁ f₁ [] X' s₂ f₂ o → Run P host s f [] X s₂ f₂ o
  | [], [], inner, inner', X, X', hX, hX', hb => by
    simp only [wrap, Option.some.injEq] at hX hX'
    subst hX hX'; exact hb
  | [], _ :: _, _, _, _, _, hX, _, _ => by simp [wrap] at hX
  | _ :: _, [], _, _, _, _, hX, _, _ => by simp [wrap] at hX
  | (m, a) :: rp, L :: ls, inner, inner', X, X', hX, hX', hb => by
    simp only [wrap, Option.bind_eq_bind] at hX hX'
    cases hpc : seqAt body rp.reverse with
    | none => simp [hpc] at hX
    | some pc =>
      cases hsg : (segment pc)[m]? with
      | none => simp [hpc, hsg] at hX
      | some sg =>
        cases ht : sg.term with
        | none => simp [hpc, hsg, ht] at hX
        | some t =>
          simp only [hpc, hsg, ht, Option.bind_some] at hX hX'
          refine wrap_mono rp ls hX hX' ?_
          intro o s₂ f₂ hr
          have hr' := Proofs.Region.run_vals_inv (vs := []) hr
          apply Proofs.Region.run_vals (vs := [])
          have hl : ∀ {o₁ : Out} {s₃ : Store H} {f₃ : Frame},
              Run P host s₁ f₁ [] [.label L.arity (if L.loop then [t] else []) inner'] s₃ f₃ o₁ →
                Run P host s f [] [.label L.arity (if L.loop then [t] else []) inner] s₃ f₃ o₁ :=
            fun h => Proofs.Region.label_back hb h
          cases hT : L.tryT
          · simp only [hT, Bool.false_eq_true, ↓reduceIte] at hr' ⊢
            exact Proofs.Region.label_back hb hr'
          · simp only [hT, ↓reduceIte] at hr' ⊢
            exact Proofs.Region.handler_back hl hr'

end Silmaril.Wasm.Cfg.Proofs.Machine

namespace Silmaril.Wasm.Cfg.Proofs.Machine

set_option linter.unusedSimpArgs false

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem seqAt_append : ∀ (p : List SeqStep) (is : List Instr) (m a : Nat),
    seqAt is (p ++ [(m, a)]) = (seqAt is p).bind fun pc => do
      let s ← (segment pc)[m]?
      let t ← s.term
      armOf t a
  | [], is, m, a => by
    simp only [List.nil_append, seqAt]
    cases h1 : (segment is)[m]? with
    | none => simp [h1]
    | some s =>
      cases h2 : s.term with
      | none => simp [h1, h2]
      | some t => cases h3 : armOf t a <;> simp [h1, h2, h3, seqAt]
  | (m', a') :: p, is, m, a => by
    simp only [List.cons_append, seqAt]
    cases h1 : (segment is)[m']? with
    | none => simp [h1]
    | some s =>
      cases h2 : s.term with
      | none => simp [h1, h2]
      | some t =>
        cases h3 : armOf t a' with
        | none => simp [h1, h2, h3]
        | some c => simp [h1, h2, h3, seqAt_append p c m a]

/-- **Entering a `block` is sound for the label invariant**: if the block's arm is not empty,
every region run of the code the machine stands for after entering is a run of the code before. -/
theorem enter_block_sound {body : Expr} {b : BlockId} {sg : Segment} {c c' : List Instr}
    {bt : BlockType} {ls : List LFrame} {s s₁ : Store H} {f f₁ : Frame} {stk ws us : List Val}
    {t₁ t₂ : List CValType} {X X' : List Admin}
    (hc : seqAt body b.seq = some c) (hsg : (segment c)[b.idx]? = some sg)
    (ht : sg.term = some (.block bt c'))
    (hr : Run P host s f stk (expression sg.body) s₁ f₁ (.normal (ws ++ us)))
    (hbt : f₁.module.blockType? bt = some (t₁, t₂)) (hm : us.length = t₁.length)
    (hX : codeAt body b stk ls = some X)
    (hX' : codeAt body ⟨b.seq ++ [(b.idx, 0)], 0⟩ us (⟨t₂.length, ws, false, false, []⟩ :: ls) =
      some X') :
    ∀ {o : Out} {s₂ : Store H} {f₂ : Frame},
      Run P host s₁ f₁ [] X' s₂ f₂ o → Run P host s f [] X s₂ f₂ o := by
  simp only [codeAt, hc, Option.bind_some] at hX
  simp [codeAt, seqAt_append, hc, hsg, ht, armOf, restAt_zero, wrap] at hX'
  refine wrap_mono b.seq.reverse ls hX hX' ?_
  intro o s₂ f₂ h
  have h' := Proofs.Region.run_vals_inv (vs := []) h
  apply Proofs.Region.run_vals (vs := [])
  rw [restAt_cons hsg]
  simp only [Segment.instrs, ht, Option.toList_some, expression, List.map_append,
    List.map_cons, List.map_nil, List.append_assoc, List.singleton_append, List.nil_append] at h' ⊢
  exact Proofs.Region.run_append hr (RunC.block hbt hm h')

end Silmaril.Wasm.Cfg.Proofs.Machine
