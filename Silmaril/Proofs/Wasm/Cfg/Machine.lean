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
  | @raise _ _ _ _ _ _ _ _ _ _ _ i _ hb ht hi =>
    left; cases hn; refine ⟨_, hb, ?_⟩
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

namespace Silmaril.Wasm.Cfg.Proofs.Machine

set_option linter.unusedSimpArgs false

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- The region step of a structured terminator into its arm: from the stack after the block's
body, running the terminator then the rest is implied by running the label (and handler) the
machine pushes. -/
theorem struct_step {s : Store H} {f : Frame} {i : Instr} {bt : BlockType} {loop tryT : Bool}
    {cs : List Catch} {stk₁ ws us : List Val} {a : Nat} {c' : List Instr}
    {t₁ t₂ : List CValType} {rest : List Admin} {s₂ : Store H} {f₂ : Frame} {o : Out}
    (hkind : StructKind i bt loop tryT cs) (harm : armOf i a = some c')
    (hcond : CondArm i stk₁ a ws us)
    (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : us.length = t₁.length)
    (h : Run P host s f ws
      ((if tryT then Admin.handler (labelArity loop t₁ t₂) cs
          [.label (labelArity loop t₁ t₂) (if loop then [i] else []) (vals us ++ expression c')]
        else .label (labelArity loop t₁ t₂) (if loop then [i] else []) (vals us ++ expression c'))
        :: rest) s₂ f₂ o) :
    Run P host s f stk₁ (.plain i :: rest) s₂ f₂ o := by
  cases hkind with
  | block =>
    cases hcond with
    | plain _ =>
      simp [armOf] at harm
      subst harm
      exact .block hbt hm (by simpa [Machine.labelArity] using h)
  | loop =>
    cases hcond with
    | plain _ =>
      simp [armOf] at harm
      subst harm
      exact .loop hbt hm (by simpa [Machine.labelArity] using h)
  | tryTable =>
    cases hcond with
    | plain _ =>
      simp [armOf] at harm
      subst harm
      exact .tryTable hbt hm (by simpa [Machine.labelArity] using h)
  | @if_ _ t e =>
    cases hcond with
    | plain hi => exact absurd rfl (hi _ _ _)
    | ifTrue hk =>
      simp [armOf] at harm
      subst harm
      refine .if_ (k := _) ?_
      split
      · rename_i h0; exact absurd h0 hk
      exact .block hbt hm (by simpa [Machine.labelArity] using h)
    | ifFalse =>
      simp [armOf] at harm
      subst harm
      refine .if_ (k := 0) ?_
      simp only [↓reduceIte]
      exact .block hbt hm (by simpa [Machine.labelArity] using h)

end Silmaril.Wasm.Cfg.Proofs.Machine

namespace Silmaril.Wasm.Cfg.Proofs.Machine

set_option linter.unusedSimpArgs false

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **Entering any structured terminator is sound for the label invariant** (`block`, `loop`,
`if` with its condition, `try_table`), for a non-empty arm. -/
theorem enter_sound {body : Expr} {b : BlockId} {sg : Segment} {c c' : List Instr} {i : Instr}
    {a : Nat} {bt : BlockType} {loop tryT : Bool} {cs : List Catch} {ls : List LFrame}
    {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ ws us : List Val} {t₁ t₂ : List CValType}
    {X X' : List Admin}
    (hc : seqAt body b.seq = some c) (hsg : (segment c)[b.idx]? = some sg)
    (ht : sg.term = some i) (harm : armOf i a = some c') (hkind : StructKind i bt loop tryT cs)
    (hr : Run P host s f stk (expression sg.body) s₁ f₁ (.normal stk₁))
    (hcond : CondArm i stk₁ a ws us)
    (hbt : f₁.module.blockType? bt = some (t₁, t₂)) (hm : us.length = t₁.length)
    (hX : codeAt body b stk ls = some X)
    (hX' : codeAt body ⟨b.seq ++ [(b.idx, a)], 0⟩ us
      (⟨labelArity loop t₁ t₂, ws, loop, tryT, cs⟩ :: ls) = some X') :
    ∀ {o : Out} {s₂ : Store H} {f₂ : Frame},
      Run P host s₁ f₁ [] X' s₂ f₂ o → Run P host s f [] X s₂ f₂ o := by
  simp only [codeAt, hc, Option.bind_some] at hX
  simp [codeAt, seqAt_append, hc, hsg, ht, harm, restAt_zero, wrap] at hX'
  refine wrap_mono b.seq.reverse ls hX hX' ?_
  intro o s₂ f₂ h
  have h' := Proofs.Region.run_vals_inv (vs := []) h
  apply Proofs.Region.run_vals (vs := [])
  rw [restAt_cons hsg]
  simp only [Segment.instrs, ht, Option.toList_some, expression, List.map_append,
    List.map_cons, List.map_nil, List.append_assoc, List.singleton_append, List.nil_append] at h' ⊢
  refine Proofs.Region.run_append hr (struct_step hkind harm hcond hbt hm ?_)
  cases tryT <;> simpa [expression] using h'

end Silmaril.Wasm.Cfg.Proofs.Machine

namespace Silmaril.Wasm.Cfg.Proofs.Machine

set_option linter.unusedSimpArgs false

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **Leaving a finished sequence is sound** (one `popL` step, Core's `label-vals` and
`handler-vals`): a region run of the parent context, with the label frame's outer values under
the finished values and the rest of the parent sequence, is a run of the context still inside
the label. -/
theorem pop_sound {body : Expr} {m a : Nat} {rp : List SeqStep} {L : LFrame} {ls : List LFrame}
    {pc : List Instr} {W : List Val} {X Y : List Admin} {s : Store H} {f : Frame}
    (hpc : seqAt body rp.reverse = some pc)
    (hX : wrap body ((m, a) :: rp) (L :: ls) (vals W) = some X)
    (hY : wrap body rp ls (vals (L.outer ++ W) ++ expression (restAt pc (m + 1))) = some Y) :
    ∀ {o : Out} {s₂ : Store H} {f₂ : Frame},
      Run P host s f [] Y s₂ f₂ o → Run P host s f [] X s₂ f₂ o := by
  simp only [wrap, hpc, Option.bind_eq_bind, Option.bind_some] at hX
  cases hsg : (segment pc)[m]? with
  | none => simp [hsg] at hX
  | some sg =>
    cases ht : sg.term with
    | none => simp [hsg, ht] at hX
    | some t =>
      simp only [hsg, ht, Option.bind_some] at hX
      refine wrap_mono rp ls hX hY ?_
      intro o s₂ f₂ h
      have h' := Proofs.Region.run_vals_inv (vs := []) h
      simp only [List.nil_append] at h'
      apply Proofs.Region.run_vals (vs := [])
      cases L.tryT
      · exact .labelNormal (Proofs.Region.run_vals_normal W) h'
      · exact .handlerNormal (.labelNormal (Proofs.Region.run_vals_normal W) .nil) (by simpa using h')

end Silmaril.Wasm.Cfg.Proofs.Machine

namespace Silmaril.Wasm.Cfg.Proofs.Machine

set_option linter.unusedSimpArgs false

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem wrap_isSome (body : Expr) : ∀ (rp : List SeqStep) (ls : List LFrame) (i i' : List Admin),
    (wrap body rp ls i).isSome = (wrap body rp ls i').isSome
  | [], [], _, _ => rfl
  | [], _ :: _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | (m, _) :: rp, L :: ls, i, i' => by
    simp only [wrap, Option.bind_eq_bind]
    cases seqAt body rp.reverse with
    | none => rfl
    | some pc =>
      simp only [Option.bind_some]
      cases (segment pc)[m]? with
      | none => rfl
      | some sg =>
        simp only [Option.bind_some]
        cases sg.term with
        | none => rfl
        | some t => simp only [Option.bind_some]; exact wrap_isSome body rp ls _ _

theorem wrap_parent_isSome {body : Expr} {m a : Nat} {rp : List SeqStep} {L : LFrame}
    {ls : List LFrame} {pc : List Instr} {i X : List Admin} (hpc : seqAt body rp.reverse = some pc)
    (hX : wrap body ((m, a) :: rp) (L :: ls) i = some X) (j : List Admin) :
    (wrap body rp ls j).isSome := by
  simp only [wrap, hpc, Option.bind_eq_bind, Option.bind_some] at hX
  cases hsg : (segment pc)[m]? with
  | none => simp [hsg] at hX
  | some sg =>
    cases ht : sg.term with
    | none => simp [hsg, ht] at hX
    | some t =>
      simp only [hsg, ht, Option.bind_some] at hX
      have := (wrap_isSome body rp ls j _).trans (congrArg Option.isSome hX)
      simpa using this

theorem depth_contRev (body : Expr) : ∀ rp : List SeqStep, depthT (contRev body rp) ≤ rp.length
  | [] => by simp [contRev, depthT]
  | (m, _) :: rp => by
    unfold contRev
    split
    · simp [depthT]
    · have := depth_contRev body rp; simp; omega

theorem restAt_none {body : Expr} {q : List SeqStep} {j : Nat} {pc : List Instr}
    (hpc : seqAt body q = some pc) (hl : (lookup body ⟨q, j⟩).isSome = false) : restAt pc j = [] := by
  rw [lookup_eq] at hl
  simp only [hpc, Option.bind_some, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hl
  exact restAt_end hl

/-- **Leaving finished sequences up to their continuation is sound**: from a context whose inner
sequence is finished (only values `W` left), going to `contRev` and popping the label frames in
between (`popL`, as `goto` does) lands on code whose region runs are runs of the context. -/
theorem cont_sound {body : Expr} {s : Store H} {f : Frame} :
    ∀ (rp : List SeqStep) (ls : List LFrame) (W : List Val) {X Y : List Admin},
      wrap body rp ls (vals W) = some X →
      codeOf body (goto (contRev body rp) rp.length ls W s f) = some Y →
      ∀ {o : Out} {s₂ : Store H} {f₂ : Frame},
        Run P host s f [] Y s₂ f₂ o → Run P host s f [] X s₂ f₂ o
  | [], [], W, X, Y, hX, hY => by
    simp [wrap] at hX; subst hX
    simp [codeOf, goto, contRev, depthT, popL] at hY; subst hY
    exact id
  | [], _ :: _, _, _, _, hX, _ => by simp [wrap] at hX
  | _ :: _, [], _, _, _, hX, _ => by simp [wrap] at hX
  | (m, a) :: rp, L :: ls, W, X, Y, hX, hY => by
    have hX0 := hX
    simp only [wrap, Option.bind_eq_bind] at hX0
    cases hpc : seqAt body rp.reverse with
    | none => simp [hpc] at hX0
    | some pc =>
      have hcont := depth_contRev body rp
      unfold contRev at hY
      split at hY
      · rename_i hl
        -- one pop: the next block of the parent sequence exists
        simp only [goto, depthT, List.length_cons, codeOf, codeAt, List.reverse_reverse,
          List.length_reverse] at hY
        rw [show rp.length + 1 - rp.length = 1 by omega] at hY
        simp only [popL, hpc, Option.bind_some] at hY
        exact pop_sound hpc hX hY
      · rename_i hl
        have hrest := restAt_none hpc (by simpa using hl)
        -- the parent sequence is finished too: pop, then continue upwards
        have hX1 : wrap body rp ls (vals (L.outer ++ W) ++ expression (restAt pc (m + 1))) =
            wrap body rp ls (vals (L.outer ++ W)) := by rw [hrest]; simp [expression]
        cases hw : wrap body rp ls (vals (L.outer ++ W)) with
        | none =>
          exfalso
          have := wrap_parent_isSome hpc hX (vals (L.outer ++ W))
          rw [hw] at this; simp at this
        | some Z =>
          intro h
          refine pop_sound hpc hX (by rw [hX1, hw]) (cont_sound rp ls (L.outer ++ W) hw ?_ h)
          simp only [goto, List.length_cons] at hY ⊢
          rw [show rp.length + 1 - depthT (contRev body rp) =
            (rp.length - depthT (contRev body rp)) + 1 by omega] at hY
          simpa [popL] using hY

end Silmaril.Wasm.Cfg.Proofs.Machine

namespace Silmaril.Wasm.Cfg.Proofs.Machine

set_option linter.unusedSimpArgs false

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **A fall-through step is sound for the label invariant**, including leaving finished
sequences (to the next block of the sequence, or up through `cont` with `popL`). -/
theorem fall_step_sound {body : Expr} {b : BlockId} {sg : Segment} {stk stk₁ : List Val}
    {ls : List LFrame} {s s₁ : Store H} {f f₁ : Frame} {X Y : List Admin}
    (hb : lookup body b = some sg) (ht : sg.term = none)
    (hr : Run P host s f stk (expression sg.body) s₁ f₁ (.normal stk₁))
    (hX : codeAt body b stk ls = some X)
    (hY : codeOf body (goto (entry body b.seq (b.idx + 1)) b.seq.length ls stk₁ s₁ f₁) = some Y) :
    ∀ {o : Out} {s₂ : Store H} {f₂ : Frame},
      Run P host s₁ f₁ [] Y s₂ f₂ o → Run P host s f [] X s₂ f₂ o := by
  obtain ⟨c, hc, hsg⟩ := seg_of_lookup hb
  simp only [codeAt, hc, Option.bind_some] at hX
  have inner : ∀ {o : Out} {s₂ : Store H} {f₂ : Frame},
      Run P host s₁ f₁ [] (vals stk₁ ++ expression (restAt c (b.idx + 1))) s₂ f₂ o →
        Run P host s f [] (vals stk ++ expression (restAt c b.idx)) s₂ f₂ o := by
    intro o s₂ f₂ h
    exact Proofs.Region.run_vals (vs := [])
      (fall_sound hsg ht hr (by simpa using Proofs.Region.run_vals_inv (vs := []) h))
  unfold entry at hY
  split at hY
  · simp only [goto, depthT, Nat.sub_self, popL, codeOf, codeAt, hc, Option.bind_some] at hY
    intro o s₂ f₂ h; exact wrap_mono _ _ hX hY inner h
  · rename_i hl
    have hrest := restAt_none hc (by simpa using hl)
    rw [hrest] at inner
    cases hw : wrap body b.seq.reverse ls (vals stk₁) with
    | none =>
      have := (wrap_isSome body b.seq.reverse ls (vals stk₁) _).trans (congrArg Option.isSome hX)
      rw [hw] at this; simp at this
    | some Z =>
      intro o s₂ f₂ h
      have hY' : codeOf body (goto (contRev body b.seq.reverse) b.seq.reverse.length ls stk₁ s₁ f₁) =
          some Y := by simpa [cont] using hY
      have h1 := cont_sound (P := P) (host := host) b.seq.reverse ls stk₁ hw hY' h
      exact wrap_mono _ _ hX hw (fun h => inner (by simpa [expression] using h)) h1

end Silmaril.Wasm.Cfg.Proofs.Machine

namespace Silmaril.Wasm.Cfg.Proofs.Machine

set_option linter.unusedSimpArgs false

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- An exception propagates through label frames that are not `try_table` handlers. -/
theorem wrap_throw {body : Expr} {s s' : Store H} {f f' : Frame} {a : Nat} :
    ∀ (rp : List SeqStep) (ls : List LFrame) {inner X : List Admin},
      (∀ L ∈ ls, L.tryT = false) → wrap body rp ls inner = some X →
      Run P host s f [] inner s' f' (.throw a) → Run P host s f [] X s' f' (.throw a)
  | [], [], _, _, _, hX, h => by simp [wrap] at hX; subst hX; exact h
  | [], _ :: _, _, _, _, hX, _ => by simp [wrap] at hX
  | _ :: _, [], _, _, _, hX, _ => by simp [wrap] at hX
  | (m, _) :: rp, L :: ls, inner, X, hT, hX, h => by
    simp only [wrap, Option.bind_eq_bind] at hX
    cases hpc : seqAt body rp.reverse with
    | none => simp [hpc] at hX
    | some pc =>
      cases hsg : (segment pc)[m]? with
      | none => simp [hpc, hsg] at hX
      | some sg =>
        cases ht : sg.term with
        | none => simp [hpc, hsg, ht] at hX
        | some t =>
          simp only [hpc, hsg, ht, Option.bind_some, hT L (by simp), Bool.false_eq_true,
            ↓reduceIte] at hX
          refine wrap_throw rp ls (fun L' hL' => hT L' (by simp [hL'])) hX ?_
          exact Proofs.Region.run_vals (vs := []) (.labelThrow h)

/-- **A raise step is sound when no enclosing frame is a handler**: the code the machine stood
for throws the same exception, with the same final store and frame. (Under a `try_table`
frame the region semantics may catch; catching is not modelled by the machine yet.) -/
theorem raise_sound {body : Expr} {b : BlockId} {sg : Segment} {stk stk₁ : List Val}
    {ls : List LFrame} {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {i : Instr} {a : Nat} {X : List Admin}
    (hb : lookup body b = some sg) (ht : sg.term = some i)
    (hr : Run P host s f stk (expression sg.body) s₁ f₁ (.normal stk₁))
    (hth : Run P host s₁ f₁ stk₁ [.plain i] s₂ f₂ (.throw a))
    (hT : ∀ L ∈ ls, L.tryT = false) (hX : codeAt body b stk ls = some X) :
    Run P host s f [] X s₂ f₂ (.throw a) := by
  obtain ⟨c, hc, hsg⟩ := seg_of_lookup hb
  simp only [codeAt, hc, Option.bind_some] at hX
  refine wrap_throw _ _ hT hX ?_
  apply Proofs.Region.run_vals (vs := [])
  rw [restAt_cons hsg]
  simp only [Segment.instrs, ht, Option.toList_some, expression, List.map_append, List.map_cons,
    List.map_nil, List.append_assoc, List.singleton_append, List.nil_append]
  have h2 := Proofs.Region.run_append (B := List.map Admin.plain (restAt c (b.idx + 1))) hth
    ⟨rfl, rfl, rfl⟩
  exact Proofs.Region.run_append hr (by simp only [Then]; simpa using h2)

end Silmaril.Wasm.Cfg.Proofs.Machine

namespace Silmaril.Wasm.Cfg.Proofs.Machine

set_option linter.unusedSimpArgs false

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- Whether the `k`-th enclosing structured instruction (at reversed path `rp`) is a `loop` in the
extracted CFG. -/
def levelLoop (body : Expr) (rp : List SeqStep) (k : Nat) : Bool :=
  match rp.drop k with
  | (m, _) :: rp' => isLoopAt body rp'.reverse m
  | [] => false

theorem drop_top {us W : List Val} {n : Nat} (h : n ≤ us.length) :
    (W ++ us).drop ((W ++ us).length - n) = us.drop (us.length - n) := by
  rw [List.length_append, show W.length + us.length - n = W.length + (us.length - n) by omega,
    List.drop_append]
  simp [List.drop_eq_nil_of_le]

/-- **Branching out of label frames to a non-loop label is sound.** The inner code branches to
the `k`-th enclosing label with values `us` (holding the label's arity). Going, as the machine
does, to that label's CFG target with its outer values under the top values is region-run
sound. -/
theorem br_lift {body : Expr} {s s₁ : Store H} {f f₁ : Frame} :
    ∀ (k : Nat) (rp : List SeqStep) (ls : List LFrame) {inner X : List Admin} {us : List Val}
      {L : LFrame},
      wrap body rp ls inner = some X → ls[k]? = some L → L.loop = false →
      levelLoop body rp k = false → L.arity ≤ us.length →
      Run P host s f [] inner s₁ f₁ (.br k us) →
      ∀ {Y : List Admin},
        codeOf body (goto ((labelsRev body rp).getD k .invalid) (rp.length - (k + 1))
          (ls.drop (k + 1)) (L.outer ++ us.drop (us.length - L.arity)) s₁ f₁) = some Y →
        ∀ {o : Out} {s₂ : Store H} {f₂ : Frame},
          Run P host s₁ f₁ [] Y s₂ f₂ o → Run P host s f [] X s₂ f₂ o
  | _, [], [], _, _, _, _, _, hL, _, _, _, _, _, _ => by simp at hL
  | _, [], _ :: _, _, _, _, _, hX, _, _, _, _, _, _, _ => by simp [wrap] at hX
  | _, _ :: _, [], _, _, _, _, _, hL, _, _, _, _, _, _ => by simp at hL
  | k, (m, a) :: rp, L₀ :: ls, inner, X, us, L, hX, hL, hloop, hlev, har, hin, Y, hY => by
    have hX0 := hX
    simp only [wrap, Option.bind_eq_bind] at hX0
    cases hpc : seqAt body rp.reverse with
    | none => simp [hpc] at hX0
    | some pc =>
      cases hsg : (segment pc)[m]? with
      | none => simp [hpc, hsg] at hX0
      | some sg =>
        cases ht : sg.term with
        | none => simp [hpc, hsg, ht] at hX0
        | some t =>
          simp only [hpc, hsg, ht, Option.bind_some] at hX0
          cases k with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hL
            subst hL
            simp only [levelLoop, List.drop_zero] at hlev
            simp only [labelsRev, hlev, Bool.false_eq_true, ↓reduceIte, List.getD_cons_zero,
              List.length_cons, Nat.add_sub_cancel, List.drop_one, List.tail_cons] at hY
            -- the label's own continuation, as in `cont_sound`, from the parent context
            have key : ∀ {o : Out} {s₂ : Store H} {f₂ : Frame},
                Run P host s₁ f₁ [] (vals (L₀.outer ++ us.drop (us.length - L₀.arity)) ++
                  expression (restAt pc (m + 1))) s₂ f₂ o →
                Run P host s f [] (vals L₀.outer ++
                  (if L₀.tryT then Admin.handler L₀.arity L₀.catches
                    [.label L₀.arity (if L₀.loop then [t] else []) inner]
                  else .label L₀.arity (if L₀.loop then [t] else []) inner) ::
                  expression (restAt pc (m + 1))) s₂ f₂ o := by
              intro o s₂ f₂ h
              have h' := Proofs.Region.run_vals_inv (vs := []) h
              simp only [List.nil_append] at h'
              apply Proofs.Region.run_vals (vs := [])
              have hsplit : us = us.take (us.length - L₀.arity) ++ us.drop (us.length - L₀.arity) :=
                (List.take_append_drop _ _).symm
              have hlen : (us.drop (us.length - L₀.arity)).length = L₀.arity := by
                simp; omega
              have hin' : Run P host s f [] inner s₁ f₁
                  (.br 0 (us.take (us.length - L₀.arity) ++ us.drop (us.length - L₀.arity))) := by
                rw [← hsplit]; exact hin
              simp only [hloop, Bool.false_eq_true, ↓reduceIte]
              have hk : Run P host s₁ f₁ L₀.outer (vals (us.drop (us.length - L₀.arity)) ++
                  expression (restAt pc (m + 1))) s₂ f₂ o := Proofs.Region.run_vals (by simpa using h')
              have hn : Run P host s₁ f₁ [] (vals (us.drop (us.length - L₀.arity)) ++
                  expression [] ++ []) s₁ f₁ (.normal (us.drop (us.length - L₀.arity))) := by
                simpa [expression] using Proofs.Region.run_vals_normal (P := P) (host := host)
                  (s := s₁) (f := f₁) (us.drop (us.length - L₀.arity))
              cases L₀.tryT
              · exact .labelBr0 hin' hlen (by simpa [expression] using hk)
              · exact .handlerNormal (.labelBr0 hin' hlen hn) (by simpa using h')
            unfold contRev at hY
            split at hY
            · simp only [goto, depthT, List.length_reverse, Nat.sub_self, popL, codeOf, codeAt,
                List.reverse_reverse, hpc, Option.bind_some] at hY
              exact wrap_mono rp ls hX0 hY key
            · rename_i hl
              have hrest := restAt_none hpc (by simpa using hl)
              rw [hrest] at key hX0
              cases hw : wrap body rp ls (vals (L₀.outer ++ us.drop (us.length - L₀.arity))) with
              | none =>
                have := wrap_parent_isSome hpc hX (vals (L₀.outer ++ us.drop (us.length - L₀.arity)))
                rw [hw] at this; simp at this
              | some Z =>
                exact fun h => wrap_mono rp ls hX0 hw (fun h => key (by simpa [expression] using h))
                  (cont_sound (P := P) (host := host) rp ls _ hw hY h)
          | succ k =>
            simp only [List.getElem?_cons_succ] at hL
            simp only [levelLoop, List.drop_succ_cons] at hlev
            have hlev' : levelLoop body rp k = false := hlev
            -- the branch leaves this frame with its outer values in front
            have hin' : Run P host s f [] (vals L₀.outer ++
                (if L₀.tryT then Admin.handler L₀.arity L₀.catches
                  [.label L₀.arity (if L₀.loop then [t] else []) inner]
                else .label L₀.arity (if L₀.loop then [t] else []) inner) ::
                expression (restAt pc (m + 1))) s₁ f₁ (.br k (L₀.outer ++ us)) := by
              apply Proofs.Region.run_vals (vs := [])
              cases L₀.tryT
              · exact .labelBrSucc hin
              · have h1 : Run P host s f [] [.label L₀.arity (if L₀.loop then [t] else []) inner]
                    s₁ f₁ (.br k us) := by
                  simpa using (RunC.labelBrSucc (C := noCall) (P := P) (host := host) (vs := [])
                    (code := []) (n := L₀.arity) (cont := if L₀.loop then [t] else []) hin)
                exact .handlerBr h1
            have har' : L.arity ≤ (L₀.outer ++ us).length := by simp; omega
            have hY' := hY
            simp only [labelsRev, List.getD_cons_succ, List.length_cons, List.drop_succ_cons] at hY'
            rw [show rp.length + 1 - (k + 1 + 1) = rp.length - (k + 1) by omega] at hY'
            exact br_lift k rp ls hX0 hL hloop hlev' har' hin' (by rw [drop_top har]; exact hY')

end Silmaril.Wasm.Cfg.Proofs.Machine

namespace Silmaril.Wasm.Cfg.Proofs.Machine

set_option linter.unusedSimpArgs false

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **A machine `br` step to a non-loop label is sound for the label invariant**, with the
step's run-time arity check. -/
theorem br_step_sound {body : Expr} {b : BlockId} {sg : Segment} {stk stk₁ : List Val}
    {ls : List LFrame} {s s₁ : Store H} {f f₁ : Frame} {l : LabelIdx} {L : LFrame}
    {X Y : List Admin} (hb : lookup body b = some sg) (ht : sg.term = some (.br l))
    (hr : Run P host s f stk (expression sg.body) s₁ f₁ (.normal stk₁))
    (hL : ls[l.toNat]? = some L) (harity : L.arity ≤ stk₁.length) (hloop : L.loop = false)
    (hlev : levelLoop body b.seq.reverse l.toNat = false)
    (hX : codeAt body b stk ls = some X)
    (hY : codeOf body (goto (resolveT (labels body b.seq) l) (b.seq.length - (l.toNat + 1))
      (ls.drop (l.toNat + 1)) (L.outer ++ stk₁.drop (stk₁.length - L.arity)) s₁ f₁) = some Y) :
    ∀ {o : Out} {s₂ : Store H} {f₂ : Frame},
      Run P host s₁ f₁ [] Y s₂ f₂ o → Run P host s f [] X s₂ f₂ o := by
  obtain ⟨c, hc, hsg⟩ := seg_of_lookup hb
  simp only [codeAt, hc, Option.bind_some] at hX
  have hin : Run P host s f [] (vals stk ++ expression (restAt c b.idx)) s₁ f₁
      (.br l.toNat stk₁) := by
    apply Proofs.Region.run_vals (vs := [])
    rw [restAt_cons hsg]
    simp only [Segment.instrs, ht, Option.toList_some, expression, List.map_append, List.map_cons,
      List.map_nil, List.append_assoc, List.singleton_append, List.nil_append]
    exact Proofs.Region.run_append hr (by simp only [Then]; exact .br)
  have hY' : codeOf body (goto ((labelsRev body b.seq.reverse).getD l.toNat .invalid)
      (b.seq.reverse.length - (l.toNat + 1)) (ls.drop (l.toNat + 1))
      (L.outer ++ stk₁.drop (stk₁.length - L.arity)) s₁ f₁) = some Y := by
    simpa [labels, resolveT, Idx.toNat] using hY
  intro o s₂ f₂ h; exact br_lift l.toNat _ ls hX hL hloop hlev harity hin hY' h

end Silmaril.Wasm.Cfg.Proofs.Machine
