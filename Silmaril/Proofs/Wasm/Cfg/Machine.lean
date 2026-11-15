module

public import Silmaril.Wasm.Cfg.Machine.Defs
public import Silmaril.Wasm.Cfg.Block.Thms
public import Silmaril.Proofs.Wasm.Cfg.Region
import Silmaril.Wasm.Execution.Core.Properties

@[expose] public section

namespace Silmaril.Wasm.Cfg.Proofs.Machine

set_option linter.unusedSimpArgs false

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics

set_option linter.unusedSimpArgs false

variable {H : Type} {P : Profile} {host : HostSemantics H}

@[simp] theorem goto_node (t : Target) (d : Nat) (ls : List LFrame) (stk : List Val) (s : Store H)
    (f : Frame) : (goto t d ls stk s f).node = t := rfl

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
    (hX' : codeAt body ⟨b.seq ++ [(b.idx, 0)], 0⟩ us (⟨t₂.length, ws, false, false, [], bt⟩ :: ls) =
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
      (⟨labelArity loop t₁ t₂, ws, loop, tryT, cs, bt⟩ :: ls) = some X') :
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
for throws the same exception, with the same final store and frame. (Handlers that let the
exception pass: `raise_pass_sound`.) -/
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
      levelLoop body rp k = false → L.arity ≤ (brVals k ls us).length →
      Run P host s f [] inner s₁ f₁ (.br k us) →
      ∀ {Y : List Admin},
        codeOf body (goto ((labelsRev body rp).getD k .invalid) (rp.length - (k + 1))
          (ls.drop (k + 1)) (L.outer ++ topVals L.arity (brVals k ls us))
          s₁ f₁) = some Y →
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
            simp only [brVals] at har hY
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
            have har' : L.arity ≤ (brVals k ls (L₀.outer ++ us)).length := by
              simpa only [brVals] using har
            have hY' := hY
            simp only [labelsRev, List.getD_cons_succ, List.length_cons, List.drop_succ_cons,
              brVals] at hY'
            rw [show rp.length + 1 - (k + 1 + 1) = rp.length - (k + 1) by omega] at hY'
            exact br_lift k rp ls hX0 hL hloop hlev' har' hin' hY'

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
    (hL : ls[l.toNat]? = some L) (harity : L.arity ≤ (brVals l.toNat ls stk₁).length)
    (hloop : L.loop = false)
    (hlev : levelLoop body b.seq.reverse l.toNat = false)
    (hX : codeAt body b stk ls = some X)
    (hY : codeOf body (goto (resolveT (labels body b.seq) l) (b.seq.length - (l.toNat + 1))
      (ls.drop (l.toNat + 1)) (L.outer ++ topVals L.arity (brVals l.toNat ls stk₁)) s₁ f₁) = some Y) :
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
      (L.outer ++ topVals L.arity (brVals l.toNat ls stk₁)) s₁ f₁) = some Y := by
    simpa [labels, resolveT, Idx.toNat] using hY
  intro o s₂ f₂ h; exact br_lift l.toNat _ ls hX hL hloop hlev harity hin hY' h

end Silmaril.Wasm.Cfg.Proofs.Machine

namespace Silmaril.Wasm.Cfg.Proofs.Machine

set_option linter.unusedSimpArgs false

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **Advancing to the next position of a sequence is sound**, given that the block's own
region code reaches the rest of the sequence from `i + 1` with stack `stk₁` (`hinner`). Covers
the next block and leaving finished sequences. -/
theorem advance_sound {body : Expr} {b : BlockId} {c : List Instr} {stk stk₁ : List Val}
    {ls : List LFrame} {s s₁ : Store H} {f f₁ : Frame} {X Y : List Admin}
    (hc : seqAt body b.seq = some c)
    (hinner : ∀ {o : Out} {s₂ : Store H} {f₂ : Frame},
      Run P host s₁ f₁ [] (vals stk₁ ++ expression (restAt c (b.idx + 1))) s₂ f₂ o →
        Run P host s f [] (vals stk ++ expression (restAt c b.idx)) s₂ f₂ o)
    (hX : codeAt body b stk ls = some X)
    (hY : codeOf body (goto (entry body b.seq (b.idx + 1)) b.seq.length ls stk₁ s₁ f₁) = some Y) :
    ∀ {o : Out} {s₂ : Store H} {f₂ : Frame},
      Run P host s₁ f₁ [] Y s₂ f₂ o → Run P host s f [] X s₂ f₂ o := by
  simp only [codeAt, hc, Option.bind_some] at hX
  unfold entry at hY
  split at hY
  · simp only [goto, depthT, Nat.sub_self, popL, codeOf, codeAt, hc, Option.bind_some] at hY
    intro o s₂ f₂ h; exact wrap_mono _ _ hX hY hinner h
  · rename_i hl
    have hrest := restAt_none hc (by simpa using hl)
    rw [hrest] at hinner
    cases hw : wrap body b.seq.reverse ls (vals stk₁) with
    | none =>
      have := (wrap_isSome body b.seq.reverse ls (vals stk₁) _).trans (congrArg Option.isSome hX)
      rw [hw] at this; simp at this
    | some Z =>
      intro o s₂ f₂ h
      have hY' : codeOf body (goto (contRev body b.seq.reverse) b.seq.reverse.length ls stk₁ s₁ f₁) =
          some Y := by simpa [cont] using hY
      have h1 := cont_sound (P := P) (host := host) b.seq.reverse ls stk₁ hw hY' h
      exact wrap_mono _ _ hX hw (fun h => hinner (by simpa [expression] using h)) h1

/-- **A `br_if` not taken is sound** (the condition is `0`: fall through). -/
theorem brIfNot_step_sound {body : Expr} {b : BlockId} {sg : Segment} {stk stk₁ : List Val}
    {ls : List LFrame} {s s₁ : Store H} {f f₁ : Frame} {l : LabelIdx} {X Y : List Admin}
    (hb : lookup body b = some sg) (ht : sg.term = some (.brIf l))
    (hr : Run P host s f stk (expression sg.body) s₁ f₁ (.normal (stk₁ ++ [.i32 0])))
    (hX : codeAt body b stk ls = some X)
    (hY : codeOf body (goto (entry body b.seq (b.idx + 1)) b.seq.length ls stk₁ s₁ f₁) = some Y) :
    ∀ {o : Out} {s₂ : Store H} {f₂ : Frame},
      Run P host s₁ f₁ [] Y s₂ f₂ o → Run P host s f [] X s₂ f₂ o := by
  obtain ⟨c, hc, hsg⟩ := seg_of_lookup hb
  refine advance_sound hc ?_ hX hY
  intro o s₂ f₂ h
  apply Proofs.Region.run_vals (vs := [])
  rw [restAt_cons hsg]
  simp only [Segment.instrs, ht, Option.toList_some, expression, List.map_append, List.map_cons,
    List.map_nil, List.append_assoc, List.singleton_append, List.nil_append]
  refine Proofs.Region.run_append hr ?_
  simp only [Then]
  exact .brIf (k := 0) (by simpa [expression] using Proofs.Region.run_vals_inv (vs := []) h)

/-- **A `br_if` taken (nonzero condition) to a non-loop label is sound**, with the step's
run-time arity check. -/
theorem brIfTaken_step_sound {body : Expr} {b : BlockId} {sg : Segment} {stk stk₁ : List Val}
    {ls : List LFrame} {s s₁ : Store H} {f f₁ : Frame} {l : LabelIdx} {L : LFrame} {k : BitVec 32}
    {X Y : List Admin} (hb : lookup body b = some sg) (ht : sg.term = some (.brIf l))
    (hr : Run P host s f stk (expression sg.body) s₁ f₁ (.normal (stk₁ ++ [.i32 k])))
    (hk : k ≠ 0) (hL : ls[l.toNat]? = some L) (harity : L.arity ≤ (brVals l.toNat ls stk₁).length)
    (hloop : L.loop = false) (hlev : levelLoop body b.seq.reverse l.toNat = false)
    (hX : codeAt body b stk ls = some X)
    (hY : codeOf body (goto (resolveT (labels body b.seq) l) (b.seq.length - (l.toNat + 1))
      (ls.drop (l.toNat + 1)) (L.outer ++ topVals L.arity (brVals l.toNat ls stk₁)) s₁ f₁) = some Y) :
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
    refine Proofs.Region.run_append hr ?_
    simp only [Then]
    refine .brIf (k := k) ?_
    split
    · rename_i h0; exact absurd h0 hk
    · exact .br
  have hY' : codeOf body (goto ((labelsRev body b.seq.reverse).getD l.toNat .invalid)
      (b.seq.reverse.length - (l.toNat + 1)) (ls.drop (l.toNat + 1))
      (L.outer ++ topVals L.arity (brVals l.toNat ls stk₁)) s₁ f₁) = some Y := by
    simpa [labels, resolveT, Idx.toNat] using hY
  intro o s₂ f₂ h; exact br_lift l.toNat _ ls hX hL hloop hlev harity hin hY' h

end Silmaril.Wasm.Cfg.Proofs.Machine

namespace Silmaril.Wasm.Cfg.Proofs.Machine

set_option linter.unusedSimpArgs false

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **Entering an empty arm is sound**: the machine pushes the frame and immediately leaves it
(`goto` to the arm sequence's continuation), as Core enters the label and leaves it with its
values (`label-vals`, `handler-vals`). -/
theorem enter_empty_sound {body : Expr} {b : BlockId} {sg : Segment} {c : List Instr} {i : Instr}
    {a : Nat} {bt : BlockType} {loop tryT : Bool} {cs : List Catch} {ls : List LFrame}
    {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ ws us : List Val} {t₁ t₂ : List CValType}
    {X Y : List Admin}
    (hc : seqAt body b.seq = some c) (hsg : (segment c)[b.idx]? = some sg)
    (ht : sg.term = some i) (harm : armOf i a = some []) (hkind : StructKind i bt loop tryT cs)
    (hr : Run P host s f stk (expression sg.body) s₁ f₁ (.normal stk₁))
    (hcond : CondArm i stk₁ a ws us)
    (hbt : f₁.module.blockType? bt = some (t₁, t₂)) (hm : us.length = t₁.length)
    (hX : codeAt body b stk ls = some X)
    (hY : codeOf body (goto (contRev body ((b.idx, a) :: b.seq.reverse)) (b.seq.length + 1)
      (⟨labelArity loop t₁ t₂, ws, loop, tryT, cs, bt⟩ :: ls) us s₁ f₁) = some Y) :
    ∀ {o : Out} {s₂ : Store H} {f₂ : Frame},
      Run P host s₁ f₁ [] Y s₂ f₂ o → Run P host s f [] X s₂ f₂ o := by
  simp only [codeAt, hc, Option.bind_some] at hX
  -- the context with the new frame around the finished (empty) arm
  have hW : wrap body ((b.idx, a) :: b.seq.reverse) (⟨labelArity loop t₁ t₂, ws, loop, tryT, cs, bt⟩ :: ls)
      (vals us) = wrap body b.seq.reverse ls (vals ws ++
        (if tryT then Admin.handler (labelArity loop t₁ t₂) cs
            [.label (labelArity loop t₁ t₂) (if loop then [i] else []) (vals us)]
          else .label (labelArity loop t₁ t₂) (if loop then [i] else []) (vals us)) ::
        expression (restAt c (b.idx + 1))) := by
    simp [wrap, hc, hsg, ht]
  cases hw : wrap body b.seq.reverse ls (vals ws ++
        (if tryT then Admin.handler (labelArity loop t₁ t₂) cs
            [.label (labelArity loop t₁ t₂) (if loop then [i] else []) (vals us)]
          else .label (labelArity loop t₁ t₂) (if loop then [i] else []) (vals us)) ::
        expression (restAt c (b.idx + 1))) with
  | none =>
    have := (wrap_isSome body b.seq.reverse ls (vals ws ++
        (if tryT then Admin.handler (labelArity loop t₁ t₂) cs
            [.label (labelArity loop t₁ t₂) (if loop then [i] else []) (vals us)]
          else .label (labelArity loop t₁ t₂) (if loop then [i] else []) (vals us)) ::
        expression (restAt c (b.idx + 1))) _).trans (congrArg Option.isSome hX)
    rw [hw] at this; simp at this
  | some Z =>
    intro o s₂ f₂ h
    have hY' : codeOf body (goto (contRev body ((b.idx, a) :: b.seq.reverse))
        ((b.idx, a) :: b.seq.reverse).length (⟨labelArity loop t₁ t₂, ws, loop, tryT, cs, bt⟩ :: ls)
        us s₁ f₁) = some Y := by simpa using hY
    have h1 := cont_sound (P := P) (host := host) _ _ us (by rw [hW, hw]) hY' h
    refine wrap_mono _ _ hX hw ?_ h1
    intro o' s₃ f₃ h'
    apply Proofs.Region.run_vals (vs := [])
    rw [restAt_cons hsg]
    simp only [Segment.instrs, ht, Option.toList_some, expression, List.map_append, List.map_cons,
      List.map_nil, List.append_assoc, List.singleton_append, List.nil_append]
    refine Proofs.Region.run_append hr (struct_step hkind harm hcond hbt hm ?_)
    have h'' := Proofs.Region.run_vals_inv (vs := []) h'
    cases tryT <;> simpa [expression] using h''

end Silmaril.Wasm.Cfg.Proofs.Machine

namespace Silmaril.Wasm.Cfg.Proofs.Machine

set_option linter.unusedSimpArgs false

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **Going to the entry of a sequence position is sound**: the code of the state `goto` lands on
(the block there, or the continuation of a finished sequence) runs as the context with the rest
of the sequence from that position. -/
theorem entry_sound {body : Expr} {p : List SeqStep} {c : List Instr} {i : Nat}
    {ls : List LFrame} {W : List Val} {s : Store H} {f : Frame} {Z Y : List Admin}
    (hc : seqAt body p = some c)
    (hZ : wrap body p.reverse ls (vals W ++ expression (restAt c i)) = some Z)
    (hY : codeOf body (goto (entry body p i) p.length ls W s f) = some Y) :
    ∀ {o : Out} {s₂ : Store H} {f₂ : Frame},
      Run P host s f [] Y s₂ f₂ o → Run P host s f [] Z s₂ f₂ o := by
  unfold entry at hY
  split at hY
  · simp [goto, depthT, popL, codeOf, codeAt, hc] at hY
    rw [hY] at hZ; cases hZ; exact fun h => h
  · rename_i hl
    have hrest := restAt_none hc (by simpa using hl)
    rw [hrest] at hZ
    have hZ' : wrap body p.reverse ls (vals W) = some Z := by simpa [expression] using hZ
    have hY' : codeOf body (goto (contRev body p.reverse) p.reverse.length ls W s f) = some Y := by
      simpa [cont] using hY
    intro o s₂ f₂ h
    exact cont_sound (P := P) (host := host) p.reverse ls W hZ' hY' h

/-- A coherent frame at a `loop` level describes a `loop` instruction with the frame's block
type. -/
theorem structKind_loop {t : Instr} {bt : BlockType} {tryT : Bool} {cs : List Catch}
    (h : StructKind t bt true tryT cs) : ∃ c, t = .loop bt c ∧ tryT = false ∧ cs = [] := by
  cases h; exact ⟨_, rfl, rfl, rfl⟩

theorem isLoopAt_of {body : Expr} {p : List SeqStep} {m : Nat} {pc : List Instr} {sg : Segment}
    {bt : BlockType} {c : List Instr} (hpc : seqAt body p = some pc)
    (hsg : (segment pc)[m]? = some sg) (ht : sg.term = some (.loop bt c)) :
    isLoopAt body p m = true := by
  have hl : lookup body ⟨p, m⟩ = some sg := by rw [lookup_eq]; simp [hpc, hsg]
  obtain ⟨sb, st⟩ := sg
  simp only at ht; subst ht
  simp [isLoopAt, hl]

/-- **Branching out of label frames to a `loop` label is sound.** The inner code branches to
the `k`-th enclosing label with values `us`; that label is a coherent `loop` frame whose block
type resolves in the branch's frame to `t₁` parameters, its arity. Re-entering the loop as the
machine does (to the loop body's entry, keeping the loop's frame, on the label's top values)
is region-run sound: Core's `label` pops to the `loop` continuation, which re-enters. -/
theorem br_lift_loop {body : Expr} {s s₁ : Store H} {f f₁ : Frame} :
    ∀ (k : Nat) (rp : List SeqStep) (ls : List LFrame) {inner X : List Admin} {us : List Val}
      {L : LFrame} {t₁ t₂ : List CValType},
      wrap body rp ls inner = some X → FramesOk body rp ls → ls[k]? = some L →
      L.loop = true → f₁.module.blockType? L.bt = some (t₁, t₂) → t₁.length = L.arity →
      L.arity ≤ (brVals k ls us).length →
      Run P host s f [] inner s₁ f₁ (.br k us) →
      ∀ {Y : List Admin},
        codeOf body (goto ((labelsRev body rp).getD k .invalid) (rp.length - k)
          (L :: ls.drop (k + 1)) (topVals L.arity (brVals k ls us)) s₁ f₁) =
          some Y →
        ∀ {o : Out} {s₂ : Store H} {f₂ : Frame},
          Run P host s₁ f₁ [] Y s₂ f₂ o → Run P host s f [] X s₂ f₂ o
  | _, [], [], _, _, _, _, _, _, _, _, hL, _, _, _, _, _, _, _ => by simp at hL
  | _, [], _ :: _, _, _, _, _, _, _, _, hok, _, _, _, _, _, _, _, _ => by simp [FramesOk] at hok
  | _, _ :: _, [], _, _, _, _, _, _, _, _, hL, _, _, _, _, _, _, _ => by simp at hL
  | k, (m, a) :: rp, L₀ :: ls, inner, X, us, L, t₁, t₂, hX, hok, hL, hloop, hbt, hlen1, har, hin,
      Y, hY => by
    have hX0 := hX
    simp only [wrap, Option.bind_eq_bind] at hX0
    obtain ⟨⟨pc', sg', t', c', hpc', hsg', ht', harm', hkind'⟩, hok'⟩ := hok
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
            simp only [brVals] at har hY
            rw [hpc] at hpc'; cases hpc'
            rw [hsg] at hsg'; cases hsg'
            rw [ht] at ht'; cases ht'
            rw [hloop] at hkind'
            obtain ⟨cb, rfl, hT, -⟩ := structKind_loop hkind'
            have ha : a = 0 ∧ c' = cb := by
              rcases a with _ | _ | a <;> simp_all [armOf]
            obtain ⟨rfl, rfl⟩ := ha
            have hil := isLoopAt_of hpc hsg ht
            simp only [labelsRev, hil, ↓reduceIte, List.getD_cons_zero, List.length_cons,
              Nat.sub_zero, List.drop_one, List.tail_cons] at hY
            have hcb : seqAt body (rp.reverse ++ [(m, 0)]) = some c' := by
              rw [seqAt_append]; simp [hpc, hsg, ht, armOf]
            set W := us.drop (us.length - L₀.arity) with hW
            -- the re-entered loop's context, one frame up
            have hZeq : wrap body (rp.reverse ++ [(m, 0)]).reverse (L₀ :: ls)
                (vals W ++ expression (restAt c' 0)) = wrap body rp ls (vals L₀.outer ++
                  .label L₀.arity [.loop L₀.bt c'] (vals W ++ expression c') ::
                  expression (restAt pc' (m + 1))) := by
              simp [wrap, hpc, hsg, ht, hT, hloop, restAt_zero]
            cases hw : wrap body rp ls (vals L₀.outer ++
                  .label L₀.arity [.loop L₀.bt c'] (vals W ++ expression c') ::
                  expression (restAt pc' (m + 1))) with
            | none =>
              have := (wrap_isSome body rp ls (vals L₀.outer ++
                  .label L₀.arity [.loop L₀.bt c'] (vals W ++ expression c') ::
                  expression (restAt pc' (m + 1))) _).trans (congrArg Option.isSome hX0)
              rw [hw] at this; simp at this
            | some Z =>
              intro h
              have hY' : codeOf body (goto (entry body (rp.reverse ++ [(m, 0)]) 0)
                  (rp.reverse ++ [(m, 0)]).length (L₀ :: ls) W s₁ f₁) = some Y := by
                simpa using hY
              have h1 := entry_sound (P := P) (host := host) hcb (by rw [hZeq, hw]) hY' h
              refine wrap_mono rp ls hX0 hw ?_ h1
              intro o' s₃ f₃ h'
              have h'' := Proofs.Region.run_vals_inv (vs := []) h'
              simp only [List.nil_append] at h''
              apply Proofs.Region.run_vals (vs := [])
              simp only [hT, hloop, Bool.false_eq_true, ↓reduceIte]
              have hsplit : us = us.take (us.length - L₀.arity) ++ W :=
                (List.take_append_drop _ _).symm
              have hWl : W.length = L₀.arity := by simp [hW]; omega
              have hin' : Run P host s f [] inner s₁ f₁
                  (.br 0 (us.take (us.length - L₀.arity) ++ W)) := by
                rw [← hsplit]; exact hin
              refine .labelBr0 hin' hWl ?_
              rw [← hlen1] at h''
              have hl := RunC.loop (C := noCall) (ws := L₀.outer) (us := W) hbt (by omega) h''
              simpa [expression, List.append_assoc] using
                Proofs.Region.run_vals (P := P) (host := host) (vs := L₀.outer) hl
          | succ k =>
            simp only [List.getElem?_cons_succ] at hL
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
            have har' : L.arity ≤ (brVals k ls (L₀.outer ++ us)).length := by
              simpa only [brVals] using har
            have hY' := hY
            simp only [labelsRev, List.getD_cons_succ, List.length_cons, List.drop_succ_cons,
              brVals] at hY'
            rw [show rp.length + 1 - (k + 1) = rp.length - k by omega] at hY'
            exact br_lift_loop k rp ls hX0 hok' hL hloop hbt hlen1 har' hin' hY'

end Silmaril.Wasm.Cfg.Proofs.Machine

namespace Silmaril.Wasm.Cfg.Proofs.Machine

set_option linter.unusedSimpArgs false

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- Under coherent frames, the CFG's `loop` flag of a level is the frame's. -/
theorem levelLoop_of_framesOk {body : Expr} :
    ∀ (k : Nat) (rp : List SeqStep) (ls : List LFrame) {L : LFrame},
      FramesOk body rp ls → ls[k]? = some L → levelLoop body rp k = L.loop
  | _, [], [], _, _, hL => by simp at hL
  | _, [], _ :: _, _, hok, _ => by simp [FramesOk] at hok
  | _, _ :: _, [], _, _, hL => by simp at hL
  | 0, (m, a) :: rp, L₀ :: ls, L, hok, hL => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hL
    subst hL
    obtain ⟨ar, ou, lp, tt, cs, bt⟩ := L₀
    obtain ⟨⟨pc, sg, t, c, hpc, hsg, ht, -, hkind⟩, -⟩ := hok
    have hl : lookup body ⟨rp.reverse, m⟩ = some sg := by rw [lookup_eq]; simp [hpc, hsg]
    obtain ⟨sb, st⟩ := sg
    simp only at ht; subst ht
    simp only [levelLoop, List.drop_zero, isLoopAt, hl]
    cases hkind <;> rfl
  | k + 1, (m, a) :: rp, L₀ :: ls, L, hok, hL => by
    simp only [List.getElem?_cons_succ] at hL
    simp only [levelLoop, List.drop_succ_cons]
    exact levelLoop_of_framesOk k rp ls hok.2 hL

/-- The code a block standing before its `br l` (or taken `br_if l`) terminator branches. -/
theorem br_code {b : BlockId} {sg : Segment} {c : List Instr} {stk stk₁ : List Val}
    {s s₁ : Store H} {f f₁ : Frame} {l : LabelIdx} {i : Instr}
    (hsg : (segment c)[b.idx]? = some sg) (ht : sg.term = some i)
    (hr : Run P host s f stk (expression sg.body) s₁ f₁ (.normal stk₁))
    (hbr : Run P host s₁ f₁ stk₁ ([.plain i] ++ expression (restAt c (b.idx + 1))) s₁ f₁
      (.br l.toNat stk₁)) :
    Run P host s f [] (vals stk ++ expression (restAt c b.idx)) s₁ f₁ (.br l.toNat stk₁) := by
  apply Proofs.Region.run_vals (vs := [])
  rw [restAt_cons hsg]
  simp only [Segment.instrs, ht, Option.toList_some, expression, List.map_append,
    List.append_assoc] at hbr ⊢
  exact Proofs.Region.run_append hr (by simp only [Then]; simpa using hbr)

/-- **A machine `br` step to a `loop` label is sound for the label invariant** (loop re-entry),
under coherent frames, with the step's run-time arity and block-type checks. -/
theorem br_loop_step_sound {body : Expr} {b : BlockId} {sg : Segment} {stk stk₁ : List Val}
    {ls : List LFrame} {s s₁ : Store H} {f f₁ : Frame} {l : LabelIdx} {L : LFrame}
    {t₁ t₂ : List CValType} {X Y : List Admin} (hb : lookup body b = some sg)
    (ht : sg.term = some (.br l))
    (hr : Run P host s f stk (expression sg.body) s₁ f₁ (.normal stk₁))
    (hL : ls[l.toNat]? = some L) (harity : L.arity ≤ (brVals l.toNat ls stk₁).length)
    (hloop : L.loop = true)
    (hbt : f₁.module.blockType? L.bt = some (t₁, t₂)) (hlen : t₁.length = L.arity)
    (hok : FramesOk body b.seq.reverse ls) (hX : codeAt body b stk ls = some X)
    (hY : codeOf body (goto (resolveT (labels body b.seq) l) (b.seq.length - l.toNat)
      (L :: ls.drop (l.toNat + 1)) (topVals L.arity (brVals l.toNat ls stk₁)) s₁ f₁) = some Y) :
    ∀ {o : Out} {s₂ : Store H} {f₂ : Frame},
      Run P host s₁ f₁ [] Y s₂ f₂ o → Run P host s f [] X s₂ f₂ o := by
  obtain ⟨c, hc, hsg⟩ := seg_of_lookup hb
  simp only [codeAt, hc, Option.bind_some] at hX
  have hin := br_code (l := l) hsg ht hr (by simpa [expression] using
    (RunC.br (C := noCall) (P := P) (host := host) (s := s₁) (f := f₁) (vs := stk₁) (l := l)
      (code := expression (restAt c (b.idx + 1)))))
  have hY' : codeOf body (goto ((labelsRev body b.seq.reverse).getD l.toNat .invalid)
      (b.seq.reverse.length - l.toNat) (L :: ls.drop (l.toNat + 1))
      (topVals L.arity (brVals l.toNat ls stk₁)) s₁ f₁) = some Y := by
    simpa [labels, resolveT, Idx.toNat] using hY
  intro o s₂ f₂ h
  exact br_lift_loop l.toNat _ ls hX hok hL hloop hbt hlen harity hin hY' h

/-- **A taken `br_if` to a `loop` label is sound** (loop re-entry), under coherent frames. -/
theorem brIfTaken_loop_step_sound {body : Expr} {b : BlockId} {sg : Segment}
    {stk stk₁ : List Val} {ls : List LFrame} {s s₁ : Store H} {f f₁ : Frame} {l : LabelIdx}
    {L : LFrame} {k : BitVec 32} {t₁ t₂ : List CValType} {X Y : List Admin}
    (hb : lookup body b = some sg) (ht : sg.term = some (.brIf l))
    (hr : Run P host s f stk (expression sg.body) s₁ f₁ (.normal (stk₁ ++ [.i32 k])))
    (hk : k ≠ 0) (hL : ls[l.toNat]? = some L) (harity : L.arity ≤ (brVals l.toNat ls stk₁).length)
    (hloop : L.loop = true) (hbt : f₁.module.blockType? L.bt = some (t₁, t₂))
    (hlen : t₁.length = L.arity) (hok : FramesOk body b.seq.reverse ls)
    (hX : codeAt body b stk ls = some X)
    (hY : codeOf body (goto (resolveT (labels body b.seq) l) (b.seq.length - l.toNat)
      (L :: ls.drop (l.toNat + 1)) (topVals L.arity (brVals l.toNat ls stk₁)) s₁ f₁) = some Y) :
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
    refine Proofs.Region.run_append hr ?_
    simp only [Then]
    refine .brIf (k := k) ?_
    split
    · rename_i h0; exact absurd h0 hk
    · exact .br
  have hY' : codeOf body (goto ((labelsRev body b.seq.reverse).getD l.toNat .invalid)
      (b.seq.reverse.length - l.toNat) (L :: ls.drop (l.toNat + 1))
      (topVals L.arity (brVals l.toNat ls stk₁)) s₁ f₁) = some Y := by
    simpa [labels, resolveT, Idx.toNat] using hY
  intro o s₂ f₂ h
  exact br_lift_loop l.toNat _ ls hX hok hL hloop hbt hlen harity hin hY' h

end Silmaril.Wasm.Cfg.Proofs.Machine

/-! ## The state invariant is preserved -/

namespace Silmaril.Wasm.Cfg.Proofs.Machine

set_option linter.unusedSimpArgs false

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem framesOk_length {body : Expr} :
    ∀ (rp : List SeqStep) (ls : List LFrame), FramesOk body rp ls → ls.length = rp.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [FramesOk] at h
  | _ :: _, [], h => by simp [FramesOk] at h
  | _ :: rp, _ :: ls, h => by simp [framesOk_length rp ls h.2]

theorem framesOk_seqAt {body : Expr} :
    ∀ (rp : List SeqStep) (ls : List LFrame), FramesOk body rp ls →
      ∃ c, seqAt body rp.reverse = some c
  | [], [], _ => ⟨body, rfl⟩
  | [], _ :: _, h => by simp [FramesOk] at h
  | _ :: _, [], h => by simp [FramesOk] at h
  | (m, a) :: rp, _ :: ls, h => by
    obtain ⟨⟨pc, sg, t, c, hpc, hsg, ht, harm, -⟩, -⟩ := h
    exact ⟨c, by rw [List.reverse_cons, seqAt_append]; simp [hpc, hsg, ht, harm]⟩

theorem framesOk_wrap {body : Expr} :
    ∀ (rp : List SeqStep) (ls : List LFrame), FramesOk body rp ls →
      ∀ inner : List Admin, ∃ X, wrap body rp ls inner = some X
  | [], [], _, inner => ⟨inner, rfl⟩
  | [], _ :: _, h, _ => by simp [FramesOk] at h
  | _ :: _, [], h, _ => by simp [FramesOk] at h
  | (m, a) :: rp, L :: ls, h, inner => by
    obtain ⟨⟨pc, sg, t, c, hpc, hsg, ht, -, -⟩, h'⟩ := h
    simp only [wrap, hpc, hsg, ht, Option.bind_eq_bind, Option.bind_some]
    exact framesOk_wrap rp ls h' _

theorem framesOk_drop {body : Expr} :
    ∀ (k : Nat) (rp : List SeqStep) (ls : List LFrame), FramesOk body rp ls →
      FramesOk body (rp.drop k) (ls.drop k)
  | 0, _, _, h => h
  | _ + 1, [], [], _ => trivial
  | _ + 1, [], _ :: _, h => by simp [FramesOk] at h
  | _ + 1, _ :: _, [], h => by simp [FramesOk] at h
  | k + 1, _ :: rp, _ :: ls, h => framesOk_drop k rp ls h.2

theorem popL_fst : ∀ (k : Nat) (ls : List LFrame) (stk : List Val), (popL k ls stk).1 = ls.drop k
  | 0, _, _ => rfl
  | _ + 1, [], _ => rfl
  | k + 1, _ :: ls, _ => popL_fst k ls _

theorem goto_succ {t : Target} {d : Nat} {L : LFrame} {ls : List LFrame} {W : List Val}
    {s : Store H} {f : Frame} (h : depthT t ≤ d) :
    goto t (d + 1) (L :: ls) W s f = goto t d ls (L.outer ++ W) s f := by
  unfold goto
  rw [show d + 1 - depthT t = (d - depthT t) + 1 by omega]
  rfl

theorem depth_contRev_cons (body : Expr) (m a : Nat) (rp : List SeqStep) :
    depthT (contRev body ((m, a) :: rp)) ≤ rp.length := by
  unfold contRev
  split
  · simp [depthT]
  · exact depth_contRev body rp

/-- Going to a sequence's continuation keeps the state invariant. -/
theorem contRev_ok {body : Expr} {s : Store H} {f : Frame} :
    ∀ (rp : List SeqStep) (ls : List LFrame) (W : List Val), FramesOk body rp ls →
      MInv body (goto (contRev body rp) rp.length ls W s f)
  | [], [], _, _ => by simp [MInv, goto, contRev, popL]
  | [], _ :: _, _, h => by simp [FramesOk] at h
  | _ :: _, [], _, h => by simp [FramesOk] at h
  | (m, a) :: rp, L :: ls, W, h => by
    rw [List.length_cons, goto_succ (depth_contRev_cons body m a rp)]
    unfold contRev
    split
    · simp only [MInv, goto, depthT, List.length_reverse, Nat.sub_self, popL,
        List.reverse_reverse]
      exact h.2
    · exact contRev_ok rp ls _ h.2

/-- Going to the entry of a sequence position keeps the state invariant. -/
theorem entry_ok {body : Expr} {s : Store H} {f : Frame} {p : List SeqStep} {i : Nat}
    {ls : List LFrame} {W : List Val} (h : FramesOk body p.reverse ls) :
    MInv body (goto (entry body p i) p.length ls W s f) := by
  unfold entry
  split
  · simpa [MInv, goto, depthT, popL] using h
  · have := contRev_ok (s := s) (f := f) p.reverse ls W h
    simpa [cont] using this

theorem labelsRev_getD {body : Expr} :
    ∀ (k : Nat) (rp : List SeqStep) {m a : Nat} {rp' : List SeqStep},
      rp.drop k = (m, a) :: rp' →
      (labelsRev body rp).getD k .invalid =
        if isLoopAt body rp'.reverse m then entry body (rp'.reverse ++ [(m, a)]) 0
        else contRev body ((m, a) :: rp')
  | 0, rp, _, _, _, h => by simp at h; subst h; simp [labelsRev]
  | _ + 1, [], _, _, _, h => by simp at h
  | k + 1, _ :: rp, _, _, _, h => by
    simp only [List.drop_succ_cons] at h
    simp only [labelsRev, List.getD_cons_succ]
    exact labelsRev_getD k rp h

theorem drop_cons_of {α : Type} {l : List α} {k : Nat} (hk : k < l.length) :
    ∃ x l', l.drop k = x :: l' ∧ l.drop (k + 1) = l' :=
  ⟨l[k], l.drop (k + 1), List.drop_eq_getElem_cons hk, rfl⟩

/-- A branch to a non-loop label keeps the state invariant. -/
theorem br_ok {body : Expr} {s : Store H} {f : Frame} {k : Nat} {rp : List SeqStep}
    {ls : List LFrame} {L : LFrame} {W : List Val} (h : FramesOk body rp ls)
    (hL : ls[k]? = some L) (hloop : L.loop = false) :
    MInv body (goto ((labelsRev body rp).getD k .invalid) (rp.length - (k + 1))
      (ls.drop (k + 1)) W s f) := by
  have hk : k < rp.length := by
    rw [← framesOk_length rp ls h]; exact (List.getElem?_eq_some_iff.mp hL).1
  obtain ⟨⟨m, a⟩, rp', hd, hd1⟩ := drop_cons_of hk
  have hlev := levelLoop_of_framesOk k rp ls h hL
  simp only [levelLoop, hd, hloop] at hlev
  rw [labelsRev_getD k rp hd, hlev]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hlen : rp.length - (k + 1) = rp'.length := by rw [← hd1]; simp
  have hok := framesOk_drop (k + 1) rp ls h
  rw [hd1] at hok
  rw [hlen]
  unfold contRev
  split
  · simpa [MInv, goto, depthT, popL] using hok
  · exact contRev_ok rp' _ W hok

/-- Re-entering a `loop` keeps the state invariant. -/
theorem br_loop_ok {body : Expr} {s : Store H} {f : Frame} {k : Nat} {rp : List SeqStep}
    {ls : List LFrame} {L : LFrame} {W : List Val} (h : FramesOk body rp ls)
    (hL : ls[k]? = some L) (hloop : L.loop = true) :
    MInv body (goto ((labelsRev body rp).getD k .invalid) (rp.length - k)
      (L :: ls.drop (k + 1)) W s f) := by
  have hkl : k < ls.length := (List.getElem?_eq_some_iff.mp hL).1
  have hk : k < rp.length := by rw [← framesOk_length rp ls h]; exact hkl
  obtain ⟨⟨m, a⟩, rp', hd, hd1⟩ := drop_cons_of hk
  have hlev := levelLoop_of_framesOk k rp ls h hL
  simp only [levelLoop, hd, hloop] at hlev
  rw [labelsRev_getD k rp hd, hlev]
  have hlen : rp.length - k = (rp'.reverse ++ [(m, a)]).length := by
    have := congrArg List.length hd; simp at this ⊢; omega
  have hok := framesOk_drop k rp ls h
  rw [hd, List.drop_eq_getElem_cons hkl] at hok
  have hLk : ls[k] = L := by simpa using (List.getElem?_eq_some_iff.mp hL).2
  rw [hLk] at hok
  simp only [↓reduceIte]
  rw [hlen]
  exact entry_ok (by simpa using hok)

/-- Entering a structured terminator keeps the state invariant. -/
theorem enter_ok {body : Expr} {s : Store H} {f : Frame} {b : BlockId} {sg : Segment}
    {i : Instr} {a : Nat} {c' : List Instr} {bt : BlockType} {loop tryT : Bool}
    {cs : List Catch} {ls : List LFrame} {n : Nat} {ws us : List Val}
    (h : FramesOk body b.seq.reverse ls) (hb : lookup body b = some sg) (ht : sg.term = some i)
    (harm : armOf i a = some c') (hkind : StructKind i bt loop tryT cs) :
    MInv body (goto (entry body (b.seq ++ [(b.idx, a)]) 0) (b.seq.length + 1)
      (⟨n, ws, loop, tryT, cs, bt⟩ :: ls) us s f) := by
  obtain ⟨c, hc, hsg⟩ := seg_of_lookup hb
  have hlen : b.seq.length + 1 = (b.seq ++ [(b.idx, a)]).length := by simp
  rw [hlen]
  refine entry_ok ?_
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, FramesOk]
  exact ⟨⟨c, sg, i, c', by simpa using hc, hsg, ht, harm, hkind⟩, h⟩

/-- A state satisfying the invariant stands for some region code. -/
theorem codeOf_of_ok {body : Expr} {st : MState H} (h : MInv body st) :
    ∃ Y, codeOf body st = some Y := by
  obtain ⟨node, stk, ls, s, f⟩ := st
  cases node with
  | block b =>
    simp only [MInv] at h
    obtain ⟨c, hc⟩ := framesOk_seqAt _ _ h
    obtain ⟨X, hX⟩ := framesOk_wrap _ _ h (vals stk ++ expression (restAt c b.idx))
    rw [List.reverse_reverse] at hc
    exact ⟨X, by simp [codeOf, codeAt, hc, hX]⟩
  | exit => simp only [MInv] at h; subst h; exact ⟨vals stk, by simp [codeOf]⟩
  | trap => exact ⟨_, rfl⟩
  | raise =>
    simp only [MInv] at h
    obtain ⟨rfl, a, rfl⟩ := h
    exact ⟨throwing a, by simp [codeOf]⟩
  | invalid => simp [MInv] at h

end Silmaril.Wasm.Cfg.Proofs.Machine

/-! ## Sinks: traps and returns through the label frames -/

namespace Silmaril.Wasm.Cfg.Proofs.Machine

set_option linter.unusedSimpArgs false

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- A trap propagates through every label frame (`label` and `handler` alike). -/
theorem wrap_trap {body : Expr} {s s' : Store H} {f f' : Frame} :
    ∀ (rp : List SeqStep) (ls : List LFrame) {inner X : List Admin},
      wrap body rp ls inner = some X →
      Run P host s f [] inner s' f' .trap → Run P host s f [] X s' f' .trap
  | [], [], _, _, hX, h => by simp [wrap] at hX; subst hX; exact h
  | [], _ :: _, _, _, hX, _ => by simp [wrap] at hX
  | _ :: _, [], _, _, hX, _ => by simp [wrap] at hX
  | (m, _) :: rp, L :: ls, inner, X, hX, h => by
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
          simp only [hpc, hsg, ht, Option.bind_some] at hX
          refine wrap_trap rp ls hX ?_
          apply Proofs.Region.run_vals (vs := [])
          cases L.tryT
          · exact .labelTrap h
          · exact .handlerTrap (by simpa using (RunC.labelTrap (C := noCall) (P := P)
              (host := host) (vs := []) (code := []) (n := L.arity)
              (cont := if L.loop then [t] else []) h))

/-- A `return` propagates through every label frame, collecting the frames' outer values under
the returned ones. -/
theorem wrap_ret {body : Expr} {s s' : Store H} {f f' : Frame} :
    ∀ (rp : List SeqStep) (ls : List LFrame) {inner X : List Admin} {us : List Val},
      wrap body rp ls inner = some X →
      Run P host s f [] inner s' f' (.ret us) → ∃ W, Run P host s f [] X s' f' (.ret (W ++ us))
  | [], [], _, _, us, hX, h => by simp [wrap] at hX; subst hX; exact ⟨[], h⟩
  | [], _ :: _, _, _, _, hX, _ => by simp [wrap] at hX
  | _ :: _, [], _, _, _, hX, _ => by simp [wrap] at hX
  | (m, _) :: rp, L :: ls, inner, X, us, hX, h => by
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
          simp only [hpc, hsg, ht, Option.bind_some] at hX
          have h1 : Run P host s f [] (vals L.outer ++
              (if L.tryT then Admin.handler L.arity L.catches
                [.label L.arity (if L.loop then [t] else []) inner]
              else .label L.arity (if L.loop then [t] else []) inner) ::
              expression (restAt pc (m + 1))) s' f' (.ret (L.outer ++ us)) := by
            apply Proofs.Region.run_vals (vs := [])
            cases L.tryT
            · exact .labelRet h
            · have h2 : Run P host s f [] [.label L.arity (if L.loop then [t] else []) inner]
                  s' f' (.ret us) := by
                simpa using (RunC.labelRet (C := noCall) (P := P) (host := host) (vs := [])
                  (code := []) (n := L.arity) (cont := if L.loop then [t] else []) h)
              exact .handlerRet h2
          obtain ⟨W, hW⟩ := wrap_ret rp ls hX h1
          exact ⟨W ++ L.outer, by simpa using hW⟩

/-- The block's code, with its terminator `i` run after the body. -/
theorem block_then {b : BlockId} {sg : Segment} {c : List Instr} {stk stk₁ : List Val}
    {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {i : Instr} {o : Out}
    (hsg : (segment c)[b.idx]? = some sg) (ht : sg.term = some i)
    (hr : Run P host s f stk (expression sg.body) s₁ f₁ (.normal stk₁))
    (hi : Run P host s₁ f₁ stk₁ (.plain i :: expression (restAt c (b.idx + 1))) s₂ f₂ o) :
    Run P host s f [] (vals stk ++ expression (restAt c b.idx)) s₂ f₂ o := by
  apply Proofs.Region.run_vals (vs := [])
  rw [restAt_cons hsg]
  simp only [Segment.instrs, ht, Option.toList_some, expression, List.map_append, List.map_cons,
    List.map_nil, List.append_assoc, List.singleton_append, List.nil_append] at hi ⊢
  exact Proofs.Region.run_append hr (by simp only [Then]; exact hi)

theorem steps_unreachable {s : Store H} {f : Frame} (stk : List Val) :
    Steps P host ⟨s, f, vals stk ++ [.plain .unreachable]⟩ ⟨s, f, [.trap]⟩ := by
  have h0 : Step P host ⟨s, f, [.plain .unreachable]⟩ ⟨s, f, [.trap]⟩ :=
    .parametric .unreachable
  cases stk with
  | nil => simpa using Relation.ReflTransGen.single h0
  | cons v vs =>
    have h1 := Step.ctxtInstrs (vs := v :: vs) (rest := []) h0 (Or.inl (by simp))
    have h2 := Step.trapInstrs (P := P) (host := host) (s := s) (f := f) (vs := v :: vs)
      (rest := []) (Or.inl (by simp))
    simp only [List.append_nil] at h1 h2
    exact Relation.ReflTransGen.head h1 (Relation.ReflTransGen.single h2)

/-- **The `unreachable` terminator is sound**: the code traps. -/
theorem trap_sound {body : Expr} {b : BlockId} {sg : Segment} {stk stk₁ : List Val}
    {ls : List LFrame} {s s₁ : Store H} {f f₁ : Frame} {X : List Admin}
    (hb : lookup body b = some sg) (ht : sg.term = some .unreachable)
    (hr : Run P host s f stk (expression sg.body) s₁ f₁ (.normal stk₁))
    (hX : codeAt body b stk ls = some X) : Run P host s f [] X s₁ f₁ .trap := by
  obtain ⟨c, hc, hsg⟩ := seg_of_lookup hb
  simp only [codeAt, hc, Option.bind_some] at hX
  refine wrap_trap _ _ hX (block_then hsg ht hr ?_)
  exact .simpleTrap (by simp [SingleThreaded.Det.famOf]) (steps_unreachable stk₁)

/-- **A trap in the block's body is sound**. -/
theorem bodyTrap_sound {body : Expr} {b : BlockId} {sg : Segment} {stk : List Val}
    {ls : List LFrame} {s s₁ : Store H} {f f₁ : Frame} {X : List Admin}
    (hb : lookup body b = some sg)
    (hr : Run P host s f stk (expression sg.body) s₁ f₁ .trap)
    (hX : codeAt body b stk ls = some X) : Run P host s f [] X s₁ f₁ .trap := by
  obtain ⟨c, hc, hsg⟩ := seg_of_lookup hb
  simp only [codeAt, hc, Option.bind_some] at hX
  refine wrap_trap _ _ hX ?_
  apply Proofs.Region.run_vals (vs := [])
  rw [restAt_cons hsg]
  simp only [Segment.instrs, expression, List.map_append, List.append_assoc, List.nil_append]
  exact Proofs.Region.run_append hr (by simp [Then])

/-- **A terminator that traps is sound**: the code traps, with the terminator's final store. -/
theorem termTrap_sound {body : Expr} {b : BlockId} {sg : Segment} {stk stk₁ : List Val}
    {ls : List LFrame} {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {i : Instr} {X : List Admin}
    (hb : lookup body b = some sg) (ht : sg.term = some i)
    (hr : Run P host s f stk (expression sg.body) s₁ f₁ (.normal stk₁))
    (hth : Run P host s₁ f₁ stk₁ [.plain i] s₂ f₂ .trap)
    (hX : codeAt body b stk ls = some X) : Run P host s f [] X s₂ f₂ .trap := by
  obtain ⟨c, hc, hsg⟩ := seg_of_lookup hb
  simp only [codeAt, hc, Option.bind_some] at hX
  refine wrap_trap _ _ hX (block_then hsg ht hr ?_)
  have h2 := Proofs.Region.run_append (B := List.map Admin.plain (restAt c (b.idx + 1)))
    (o := .trap) (s' := s₂) (f' := f₂) hth (by simp [Then])
  simpa [expression] using h2

/-- **A `return` is sound**: the code returns the block's values, over the frames' outer
values. -/
theorem ret_sound {body : Expr} {b : BlockId} {sg : Segment} {stk stk₁ : List Val}
    {ls : List LFrame} {s s₁ : Store H} {f f₁ : Frame} {X : List Admin}
    (hb : lookup body b = some sg) (ht : sg.term = some .return_)
    (hr : Run P host s f stk (expression sg.body) s₁ f₁ (.normal stk₁))
    (hX : codeAt body b stk ls = some X) : ∃ W, Run P host s f [] X s₁ f₁ (.ret (W ++ stk₁)) := by
  obtain ⟨c, hc, hsg⟩ := seg_of_lookup hb
  simp only [codeAt, hc, Option.bind_some] at hX
  exact wrap_ret _ _ hX (block_then hsg ht hr .ret)

end Silmaril.Wasm.Cfg.Proofs.Machine

/-! ## Handler catching -/

namespace Silmaril.Wasm.Cfg.Proofs.Machine

set_option linter.unusedSimpArgs false

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- An exception propagates through label frames whose handlers all let it pass. -/
theorem wrap_throw_pass {body : Expr} {s s' : Store H} {f f' : Frame} {a : Nat} :
    ∀ (rp : List SeqStep) (ls : List LFrame) {inner X : List Admin},
      (∀ (k : Nat) (L : LFrame), ls[k]? = some L → L.tryT = true →
        Catches s' f' a L.catches none) →
      wrap body rp ls inner = some X →
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
          simp only [hpc, hsg, ht, Option.bind_some] at hX
          refine wrap_throw_pass rp ls (fun k L' hk => hT (k + 1) L' (by simpa using hk)) hX ?_
          apply Proofs.Region.run_vals (vs := [])
          cases hL : L.tryT
          · simp only [Bool.false_eq_true, ↓reduceIte]
            exact .labelThrow h
          · simp only [↓reduceIte]
            exact .handlerRethrow (by simpa using (RunC.labelThrow (C := noCall) (P := P)
              (host := host) (vs := []) (code := []) (n := L.arity)
              (cont := if L.loop then [t] else []) h)) (hT 0 L (by simp) hL)

/-- **An uncaught raise step is sound**: the code throws the same exception, with the same final
store and frame, when every enclosing handler lets it pass. -/
theorem raise_pass_sound {body : Expr} {b : BlockId} {sg : Segment} {stk stk₁ : List Val}
    {ls : List LFrame} {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {i : Instr} {a : Nat}
    {X : List Admin} (hb : lookup body b = some sg) (ht : sg.term = some i)
    (hr : Run P host s f stk (expression sg.body) s₁ f₁ (.normal stk₁))
    (hth : Run P host s₁ f₁ stk₁ [.plain i] s₂ f₂ (.throw a))
    (hT : ∀ (k : Nat) (L : LFrame), ls[k]? = some L → L.tryT = true →
      Catches s₂ f₂ a L.catches none)
    (hX : codeAt body b stk ls = some X) :
    Run P host s f [] X s₂ f₂ (.throw a) := by
  obtain ⟨c, hc, hsg⟩ := seg_of_lookup hb
  simp only [codeAt, hc, Option.bind_some] at hX
  refine wrap_throw_pass _ _ hT hX (block_then hsg ht hr ?_)
  have h2 := Proofs.Region.run_append (B := List.map Admin.plain (restAt c (b.idx + 1))) hth
    ⟨rfl, rfl, rfl⟩
  simpa [expression] using h2

/-- What a branch to the `k`-th label with values `V` out of the context `rp, ls` (code `X`)
proves: for the label's frame, under the machine's run-time checks, going where the machine
goes is region-run sound. -/
def BrOut (P : Profile) (host : HostSemantics H) (body : Expr) (rp : List SeqStep)
    (ls : List LFrame) (X : List Admin) (s : Store H) (f : Frame) (k : Nat) (V : List Val)
    (s₁ : Store H) (f₁ : Frame) : Prop :=
  ∀ L : LFrame, ls[k]? = some L → L.arity ≤ V.length →
    (L.loop = true → ∃ t₁ t₂, f₁.module.blockType? L.bt = some (t₁, t₂) ∧
      t₁.length = L.arity) →
    ∀ {Y : List Admin},
      codeOf body (if L.loop then
          goto ((labelsRev body rp).getD k .invalid) (rp.length - k) (L :: ls.drop (k + 1))
            (V.drop (V.length - L.arity)) s₁ f₁
        else
          goto ((labelsRev body rp).getD k .invalid) (rp.length - (k + 1)) (ls.drop (k + 1))
            (L.outer ++ V.drop (V.length - L.arity)) s₁ f₁) = some Y →
      ∀ {o : Out} {s₂ : Store H} {f₂ : Frame},
        Run P host s₁ f₁ [] Y s₂ f₂ o → Run P host s f [] X s₂ f₂ o

/-- A branch out of coherent frames, to a loop or not, is sound. -/
theorem br_out {body : Expr} {rp : List SeqStep} {ls : List LFrame} {inner X : List Admin}
    {s s₁ : Store H} {f f₁ : Frame} {k : Nat} {V : List Val} (hok : FramesOk body rp ls)
    (hX : wrap body rp ls inner = some X) (hin : Run P host s f [] inner s₁ f₁ (.br k V)) :
    BrOut P host body rp ls X s f k (brVals k ls V) s₁ f₁ := by
  intro L hL har hlbt Y hY o s₂ f₂ h
  cases hl : L.loop
  · simp only [hl, Bool.false_eq_true, ↓reduceIte] at hY
    exact br_lift k rp ls hX hL hl ((levelLoop_of_framesOk k rp ls hok hL).trans hl) har hin hY h
  · simp only [hl, ↓reduceIte] at hY
    obtain ⟨t₁, t₂, hbt, hlen⟩ := hlbt hl
    exact br_lift_loop k rp ls hX hok hL hl hbt hlen har hin hY h

theorem brOut_succ {body : Expr} {rp : List SeqStep} {ls : List LFrame} {X : List Admin}
    {s s₁ : Store H} {f f₁ : Frame} {k : Nat} {V : List Val} {m a : Nat} {L₀ : LFrame}
    (h : BrOut P host body rp ls X s f k V s₁ f₁) :
    BrOut P host body ((m, a) :: rp) (L₀ :: ls) X s f (k + 1) V s₁ f₁ := by
  intro L hL har hlbt Y hY
  simp only [List.getElem?_cons_succ] at hL
  refine h L hL har hlbt ?_
  have e1 : ((m, a) :: rp).length - (k + 1) = rp.length - k := by simp
  have e2 : ((m, a) :: rp).length - (k + 1 + 1) = rp.length - (k + 1) := by simp
  simpa only [labelsRev, List.getD_cons_succ, e1, e2, List.drop_succ_cons] using hY

/-- **A thrown exception caught by the `j`-th frame branches**: the frames below `j` let it
pass, frame `j`'s handler catches it with values `us` to label `l`; that is a branch to label
`j + 1 + l` of the context, with the handler's outer values under `us`. -/
theorem throw_lift {body : Expr} {s s₁ : Store H} {f f₁ : Frame} {a : Nat} {us : List Val}
    {l : LabelIdx} :
    ∀ (j : Nat) (rp : List SeqStep) (ls : List LFrame) {inner X : List Admin} {L : LFrame},
      FramesOk body rp ls → wrap body rp ls inner = some X →
      Run P host s f [] inner s₁ f₁ (.throw a) →
      (∀ (k : Nat) (L : LFrame), k < j → ls[k]? = some L → L.tryT = true →
        Catches s₁ f₁ a L.catches none) →
      ls[j]? = some L → L.tryT = true → Catches s₁ f₁ a L.catches (some (us, l)) →
      BrOut P host body rp ls X s f (j + 1 + l.toNat) (brVals l.toNat (ls.drop (j + 1)) (L.outer ++ us))
        s₁ f₁
  | _, [], [], _, _, _, _, _, _, _, hL, _, _ => by simp at hL
  | _, [], _ :: _, _, _, _, hok, _, _, _, _, _, _ => by simp [FramesOk] at hok
  | _, _ :: _, [], _, _, _, _, _, _, _, hL, _, _ => by simp at hL
  | j, (m, a') :: rp, L₀ :: ls, inner, X, L, hok, hX, hin, hpass, hL, hT, hc => by
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
          have hlab : Run P host s f [] [.label L₀.arity (if L₀.loop then [t] else []) inner]
              s₁ f₁ (.throw a) := by
            simpa using (RunC.labelThrow (C := noCall) (P := P) (host := host) (vs := [])
              (code := []) (n := L₀.arity) (cont := if L₀.loop then [t] else []) hin)
          cases j with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hL
            subst hL
            simp only [hT, ↓reduceIte] at hX0
            have hrun : Run P host s f [] (vals L₀.outer ++
                Admin.handler L₀.arity L₀.catches
                  [.label L₀.arity (if L₀.loop then [t] else []) inner] ::
                expression (restAt pc (m + 1))) s₁ f₁ (.br l.toNat (L₀.outer ++ us)) := by
              apply Proofs.Region.run_vals (vs := [])
              simpa using (RunC.handlerCatch (C := noCall) (P := P) (host := host)
                (vs := L₀.outer) (code := expression (restAt pc (m + 1))) hlab hc)
            have := brOut_succ (m := m) (a := a') (L₀ := L₀) (br_out hok.2 hX0 hrun)
            simpa [Nat.add_comm] using this
          | succ j =>
            simp only [List.getElem?_cons_succ] at hL
            have hrun : Run P host s f [] (vals L₀.outer ++
                (if L₀.tryT then Admin.handler L₀.arity L₀.catches
                  [.label L₀.arity (if L₀.loop then [t] else []) inner]
                else .label L₀.arity (if L₀.loop then [t] else []) inner) ::
                expression (restAt pc (m + 1))) s₁ f₁ (.throw a) := by
              apply Proofs.Region.run_vals (vs := [])
              cases hT0 : L₀.tryT
              · simp only [Bool.false_eq_true, ↓reduceIte]
                exact .labelThrow hin
              · simp only [↓reduceIte]
                exact .handlerRethrow hlab (hpass 0 L₀ (by omega) (by simp) hT0)
            have := brOut_succ (m := m) (a := a') (L₀ := L₀)
              (throw_lift j rp ls hok.2 hX0 hrun
                (fun k L' hk hL' hT' => hpass (k + 1) L' (by omega) (by simpa using hL') hT')
                hL hT hc)
            have e : j + 1 + l.toNat + 1 = j + 1 + 1 + l.toNat := by omega
            rw [e] at this
            simpa only [List.drop_succ_cons] using this

/-- **A caught throw is sound**: the machine's branch to the catching clause's label runs as the
code the block stood for. -/
theorem catch_step_sound {body : Expr} {b : BlockId} {sg : Segment} {stk stk₁ us : List Val}
    {ls : List LFrame} {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {i : Instr} {a j : Nat}
    {L L' : LFrame} {l : LabelIdx} {X Y : List Admin}
    (hb : lookup body b = some sg) (ht : sg.term = some i)
    (hr : Run P host s f stk (expression sg.body) s₁ f₁ (.normal stk₁))
    (hth : Run P host s₁ f₁ stk₁ [.plain i] s₂ f₂ (.throw a))
    (hpass : ∀ (k : Nat) (L : LFrame), k < j → ls[k]? = some L → L.tryT = true →
      Catches s₂ f₂ a L.catches none)
    (hL : ls[j]? = some L) (hT : L.tryT = true) (hc : Catches s₂ f₂ a L.catches (some (us, l)))
    (hL' : ls[j + 1 + l.toNat]? = some L')
    (harity : L'.arity ≤ (brVals l.toNat (ls.drop (j + 1)) (L.outer ++ us)).length)
    (hlbt : L'.loop = true → ∃ t₁ t₂, f₂.module.blockType? L'.bt = some (t₁, t₂) ∧
      t₁.length = L'.arity)
    (hok : FramesOk body b.seq.reverse ls) (hX : codeAt body b stk ls = some X)
    (hY : codeOf body (if L'.loop then
          goto ((labels body b.seq).getD (j + 1 + l.toNat) .invalid)
            (b.seq.length - (j + 1 + l.toNat)) (L' :: ls.drop (j + 1 + l.toNat + 1))
            (topVals L'.arity (brVals l.toNat (ls.drop (j + 1)) (L.outer ++ us))) s₂ f₂
        else
          goto ((labels body b.seq).getD (j + 1 + l.toNat) .invalid)
            (b.seq.length - (j + 1 + l.toNat + 1)) (ls.drop (j + 1 + l.toNat + 1))
            (L'.outer ++ topVals L'.arity (brVals l.toNat (ls.drop (j + 1)) (L.outer ++ us)))
            s₂ f₂) =
        some Y) :
    ∀ {o : Out} {s₃ : Store H} {f₃ : Frame},
      Run P host s₂ f₂ [] Y s₃ f₃ o → Run P host s f [] X s₃ f₃ o := by
  obtain ⟨c, hc', hsg⟩ := seg_of_lookup hb
  simp only [codeAt, hc', Option.bind_some] at hX
  have hin : Run P host s f [] (vals stk ++ expression (restAt c b.idx)) s₂ f₂ (.throw a) := by
    refine block_then hsg ht hr ?_
    have h2 := Proofs.Region.run_append (B := List.map Admin.plain (restAt c (b.idx + 1))) hth
      ⟨rfl, rfl, rfl⟩
    simpa [expression] using h2
  have hbo := throw_lift j _ ls hok hX hin hpass hL hT hc
  intro o s₃ f₃ h
  exact hbo L' hL' harity hlbt (by simpa [labels] using hY) h

theorem catches_label {s : Store H} {f : Frame} {a : Nat} {cs : List Catch} {us : List Val}
    {l : LabelIdx} (h : Catches s f a cs (some (us, l))) : ∃ cl ∈ cs, catchLabel cl = l := by
  generalize hr : (some (us, l) : Option (List Val × LabelIdx)) = r at h
  induction h with
  | catch_ => cases hr; exact ⟨_, List.mem_cons_self .., rfl⟩
  | catchRef => cases hr; exact ⟨_, List.mem_cons_self .., rfl⟩
  | catchAll => cases hr; exact ⟨_, List.mem_cons_self .., rfl⟩
  | catchAllRef => cases hr; exact ⟨_, List.mem_cons_self .., rfl⟩
  | next _ _ ih =>
    obtain ⟨cl, hcl, he⟩ := ih hr
    exact ⟨cl, List.mem_cons_of_mem _ hcl, he⟩
  | empty => cases hr

end Silmaril.Wasm.Cfg.Proofs.Machine

/-! ## Whole runs -/

namespace Silmaril.Wasm.Cfg.Proofs.Machine

set_option linter.unusedSimpArgs false

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem resolveT_labels (body : Expr) (p : List SeqStep) (l : LabelIdx) :
    resolveT (labels body p) l = (labelsRev body p.reverse).getD l.toNat .invalid := by
  simp [labels, resolveT, Idx.toNat]

/-- What one machine step proves: the invariant holds after it, and either the next state's
code runs as the current one's (`Y`), or the step reached a sink and the current code ends as
that sink says (`Ends`). -/
def StepOk (body : Expr) (st st₁ : MState H) (X : List Admin) : Prop :=
  MInv body st₁ ∧
    ((∃ Y, codeOf body st₁ = some Y ∧ ∀ {o : Out} {s₂ : Store H} {f₂ : Frame},
        Run P host st₁.store st₁.frame [] Y s₂ f₂ o → Run P host st.store st.frame [] X s₂ f₂ o) ∨
      ∃ o, Ends st₁ o ∧ Run P host st.store st.frame [] X st₁.store st₁.frame o)

theorem stepOk_back {body : Expr} {st st₁ : MState H} {X : List Admin} (hok₁ : MInv body st₁)
    (hb : ∀ {Y : List Admin}, codeOf body st₁ = some Y → ∀ {o : Out} {s₂ : Store H} {f₂ : Frame},
      Run P host st₁.store st₁.frame [] Y s₂ f₂ o → Run P host st.store st.frame [] X s₂ f₂ o) :
    StepOk (P := P) (host := host) body st st₁ X := by
  obtain ⟨Y, hY⟩ := codeOf_of_ok hok₁
  exact ⟨hok₁, Or.inl ⟨Y, hY, hb hY⟩⟩

/-- **Every machine step is sound** for the state invariant and the region code it stands for. -/
theorem mstep_sound {body : Expr} {st st₁ : MState H} (h : MStep P host body st st₁)
    (hok : MInv body st) {X : List Admin} (hX : codeOf body st = some X) :
    StepOk (P := P) (host := host) body st st₁ X := by
  cases h with
  | fall hb ht hr =>
    simp only [MInv] at hok; simp only [codeOf] at hX
    exact stepOk_back (entry_ok hok) (fun hY => fall_step_sound hb ht hr hX hY)
  | brIfNot hb ht hr =>
    simp only [MInv] at hok; simp only [codeOf] at hX
    exact stepOk_back (entry_ok hok) (fun hY => brIfNot_step_sound hb ht hr hX hY)
  | @br b sg stk stk₁ ls s s₁ f f₁ l L hb ht hr hL harity hlbt =>
    simp only [MInv] at hok; simp only [codeOf] at hX
    cases hl : L.loop
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine stepOk_back ?_ (fun hY => br_step_sound hb ht hr hL harity hl
        ((levelLoop_of_framesOk _ _ _ hok hL).trans hl) hX hY)
      rw [resolveT_labels, ← List.length_reverse (as := b.seq)]
      exact br_ok hok hL hl
    · obtain ⟨t₁, t₂, hbt, hlen⟩ := hlbt hl
      simp only [↓reduceIte]
      refine stepOk_back ?_ (fun hY => br_loop_step_sound hb ht hr hL harity hl hbt hlen hok hX hY)
      rw [resolveT_labels, ← List.length_reverse (as := b.seq)]
      exact br_loop_ok hok hL hl
  | @brIfTaken b sg stk stk₁ ls s s₁ f f₁ l L k hb ht hr hk hL harity hlbt =>
    simp only [MInv] at hok; simp only [codeOf] at hX
    cases hl : L.loop
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine stepOk_back ?_ (fun hY => brIfTaken_step_sound hb ht hr hk hL harity hl
        ((levelLoop_of_framesOk _ _ _ hok hL).trans hl) hX hY)
      rw [resolveT_labels, ← List.length_reverse (as := b.seq)]
      exact br_ok hok hL hl
    · obtain ⟨t₁, t₂, hbt, hlen⟩ := hlbt hl
      simp only [↓reduceIte]
      refine stepOk_back ?_
        (fun hY => brIfTaken_loop_step_sound hb ht hr hk hL harity hl hbt hlen hok hX hY)
      rw [resolveT_labels, ← List.length_reverse (as := b.seq)]
      exact br_loop_ok hok hL hl
  | @enter b sg stk stk₁ ws us ls s s₁ f f₁ i a c bt t₁ t₂ loop tryT cs hb ht harm hkind hr hcond
      hbt hm =>
    simp only [MInv] at hok; simp only [codeOf] at hX
    obtain ⟨c₀, hc, hsg⟩ := seg_of_lookup hb
    refine stepOk_back (enter_ok hok hb ht harm hkind) ?_
    intro Y hY o s₂ f₂ hR
    have hc' : seqAt body (b.seq ++ [(b.idx, a)]) = some c := by
      rw [seqAt_append]; simp [hc, hsg, ht, harm]
    by_cases hl : (lookup body ⟨b.seq ++ [(b.idx, a)], 0⟩).isSome
    · simp only [entry, hl, ↓reduceIte, goto, depthT, List.length_append, List.length_cons,
        List.length_nil, Nat.sub_self, popL, codeOf] at hY
      exact enter_sound hc hsg ht harm hkind hr hcond hbt hm hX hY hR
    · have hnil : c = [] := by
        have := restAt_none hc' (by simpa using hl)
        rwa [restAt_zero] at this
      subst hnil
      have hY' : codeOf body (goto (contRev body ((b.idx, a) :: b.seq.reverse))
          (b.seq.length + 1) (⟨labelArity loop t₁ t₂, ws, loop, tryT, cs, bt⟩ :: ls) us s₁ f₁) =
          some Y := by
        simpa [entry, hl, cont] using hY
      exact enter_empty_sound hc hsg ht harm hkind hr hcond hbt hm hX hY' hR
  | @ret b sg stk stk₁ ls s s₁ f f₁ hb ht hr =>
    simp only [codeOf] at hX
    obtain ⟨W, hW⟩ := ret_sound hb ht hr hX
    exact ⟨by simp [MInv], Or.inr ⟨_, by simp only [Ends]; exact Or.inr ⟨W, rfl⟩, hW⟩⟩
  | trap hb ht hr =>
    simp only [codeOf] at hX
    obtain ⟨stk₁, hr⟩ := hr
    exact ⟨by simp [MInv], Or.inr ⟨.trap, by simp [Ends], trap_sound hb ht hr hX⟩⟩
  | bodyTrap hb hr =>
    simp only [codeOf] at hX
    exact ⟨by simp [MInv], Or.inr ⟨.trap, by simp [Ends], bodyTrap_sound hb hr hX⟩⟩
  | termTrap hb ht hr hth =>
    simp only [codeOf] at hX
    exact ⟨by simp [MInv], Or.inr ⟨.trap, by simp [Ends], termTrap_sound hb ht hr hth hX⟩⟩
  | @catch_ b sg stk stk₁ us ls s s₁ s₂ f f₁ f₂ i a j L L' l hb ht hi hr hth hpass hL hT hc hL'
      harity hlbt =>
    simp only [MInv] at hok; simp only [codeOf] at hX
    cases hl : L'.loop
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine stepOk_back ?_ (fun hY => catch_step_sound hb ht hr hth hpass hL hT hc hL' harity hlbt
        hok hX (by simp only [hl, Bool.false_eq_true, ↓reduceIte]; exact hY))
      simp only [labels]
      rw [← List.length_reverse (as := b.seq)]
      exact br_ok hok hL' hl
    · simp only [↓reduceIte]
      refine stepOk_back ?_ (fun hY => catch_step_sound hb ht hr hth hpass hL hT hc hL' harity hlbt
        hok hX (by simp only [hl, ↓reduceIte]; exact hY))
      simp only [labels]
      rw [← List.length_reverse (as := b.seq)]
      exact br_loop_ok hok hL' hl
  | @raise b sg stk stk₁ ls s s₁ s₂ f f₁ f₂ i a hb ht hi hr hth hT =>
    simp only [codeOf] at hX
    exact ⟨by simp [MInv], Or.inr ⟨.throw a, by simp [Ends], raise_pass_sound hb ht hr hth hT hX⟩⟩

/-- A sink state's own code ends as the sink says. -/
theorem sink_sound {body : Expr} {st : MState H} (hs : st.node.IsSink) {X : List Admin}
    (hX : codeOf body st = some X) :
    ∃ o, Ends st o ∧ Run P host st.store st.frame [] X st.store st.frame o := by
  obtain ⟨node, stk, ls, s, f⟩ := st
  cases node with
  | exit =>
    simp only [codeOf] at hX
    split at hX
    · cases hX; exact ⟨.normal stk, by simp [Ends], Proofs.Region.run_vals_normal stk⟩
    · cases hX
  | trap =>
    simp only [codeOf] at hX; cases hX
    exact ⟨.trap, by simp [Ends], .trap⟩
  | raise =>
    simp only [codeOf] at hX
    split at hX
    · rename_i _ a
      split at hX
      · cases hX
        exact ⟨.throw a, by simp [Ends], .val (v := .ref (.exn a)) rfl (.throwRefExn (ws := []))⟩
      · cases hX
    · cases hX
  | block b => simp [Target.IsSink] at hs
  | invalid => simp [Target.IsSink] at hs

theorem ends_not_block {st : MState H} {o : Out} (hE : Ends st o) {b : BlockId}
    (hb : st.node = .block b) : False := by
  obtain ⟨node, stk, ls, s, f⟩ := st
  simp only at hb; subst hb
  simp [Ends] at hE

/-- **Whole-run soundness**: a machine run from a state satisfying the invariant to a sink is a
region run of the code the state stands for, ending as the sink says. -/
theorem run_sound {body : Expr} {st st' : MState H}
    (h : Relation.ReflTransGen (MStep P host body) st st') (hs : st'.node.IsSink)
    (hok : MInv body st) {X : List Admin} (hX : codeOf body st = some X) :
    ∃ o, Ends st' o ∧ Run P host st.store st.frame [] X st'.store st'.frame o := by
  induction h using Relation.ReflTransGen.head_induction_on generalizing X with
  | refl => exact sink_sound hs hX
  | head hstep hrest ih =>
    obtain ⟨hok₁, ⟨Y, hY, hb⟩ | ⟨o, hE, hR⟩⟩ := mstep_sound hstep hok hX
    · obtain ⟨o, hE, hR⟩ := ih hok₁ hY
      exact ⟨o, hE, hb hR⟩
    · rcases hrest.cases_head with rfl | ⟨c, hc, -⟩
      · exact ⟨o, hE, hR⟩
      · exfalso
        obtain ⟨b, hb⟩ := mstep_from_block hc
        exact ends_not_block hE hb

/-- **Whole-run soundness from the CFG entry**: a machine run of a function body from its
initial state (`cfgEntry`, empty stack, no frames) to a sink is a region run of the body. -/
theorem run_sound_initial {body : Expr} {s : Store H} {f : Frame} {st' : MState H}
    (h : Relation.ReflTransGen (MStep P host body) (initial body s f) st')
    (hs : st'.node.IsSink) :
    ∃ o, Ends st' o ∧ Run P host s f [] (expression body) st'.store st'.frame o := by
  have hinit : initial body s f = goto (entry body [] 0) ([] : List SeqStep).length [] [] s f := by
    simp [initial, goto, popL, cfgEntry]
  have hok : MInv body (initial body s f) := by
    rw [hinit]; exact entry_ok (p := []) trivial
  obtain ⟨Y, hY⟩ := codeOf_of_ok hok
  obtain ⟨o, hE, hR⟩ := run_sound h hs hok hY
  refine ⟨o, hE, ?_⟩
  rw [hinit] at hY
  exact entry_sound (p := []) (c := body) (i := 0) rfl (by simp [wrap, restAt_zero, vals]) hY hR

end Silmaril.Wasm.Cfg.Proofs.Machine


/-! ## Machine steps follow the extracted CFG -/

namespace Silmaril.Wasm.Cfg.Proofs.Machine

set_option linter.unusedSimpArgs false

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem structKind_tryT {t : Instr} {bt : BlockType} {lp : Bool} {cs : List Catch}
    (h : StructKind t bt lp true cs) : ∃ c, t = .tryTable bt cs c := by
  cases h; exact ⟨_, rfl⟩

theorem labelsRev_getD_drop (body : Expr) :
    ∀ (n : Nat) (rp : List SeqStep) (k : Nat), n ≤ rp.length →
      (labelsRev body rp).getD (n + k) .invalid = (labelsRev body (rp.drop n)).getD k .invalid
  | 0, _, _, _ => by simp
  | _ + 1, [], _, h => by simp at h
  | n + 1, _ :: rp, k, h => by
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [labelsRev, List.getD_cons_succ, List.drop_succ_cons]
    exact labelsRev_getD_drop body n rp k (by simp at h; omega)

/-- **Every machine step from a state satisfying the invariant follows the extracted CFG**: an
edge of its block, a trap of the block's body (an instruction effect, not a flow edge), or a
catch edge of an enclosing `try_table` (`CatchEdge`). -/
theorem mstep_edge {body : Expr} {st st' : MState H} (h : MStep P host body st st')
    (hok : MInv body st) {b : BlockId} (hn : st.node = .block b) :
    Edge body b st'.node ∨ st'.node = .trap ∨ CatchEdge body b st'.node := by
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
  | bodyTrap => right; left; rfl
  | termTrap => right; left; rfl
  | @raise _ _ _ _ _ _ _ _ _ _ _ i _ hb ht hi =>
    left; cases hn; refine ⟨_, hb, ?_⟩
    cases i <;> simp_all [Instr.IsThrow, succOf]
  | @catch_ b' sg stk stk₁ us ls s s₁ s₂ f f₁ f₂ i a j L L' l hb ht hi hr hth hpass hL hT hc hL'
      harity hlbt =>
    right; right; cases hn
    simp only [MInv] at hok
    have hjl : j < ls.length := (List.getElem?_eq_some_iff.mp hL).1
    have hk : j < b.seq.reverse.length := by rw [← framesOk_length _ _ hok]; exact hjl
    obtain ⟨⟨m, a'⟩, rp, hd, hd1⟩ := drop_cons_of hk
    have hokj := framesOk_drop j _ _ hok
    have hLj : ls[j] = L := by simpa using (List.getElem?_eq_some_iff.mp hL).2
    rw [hd, List.drop_eq_getElem_cons hjl, hLj] at hokj
    obtain ⟨⟨pc, sg', t, c', hpc, hsg', ht', -, hkind⟩, -⟩ := hokj
    rw [hT] at hkind
    obtain ⟨cb, rfl⟩ := structKind_tryT hkind
    obtain ⟨cl, hcl, hcle⟩ := catches_label hc
    have hseq : b.seq = rp.reverse ++ (m, a') :: (b.seq.reverse.take j).reverse := by
      have := List.take_append_drop j b.seq.reverse
      rw [hd] at this
      have h2 := congrArg List.reverse this
      simp only [List.reverse_reverse, List.reverse_append, List.reverse_cons] at h2
      simpa using h2.symm
    have hlk : lookup body ⟨rp.reverse, m⟩ = some sg' := by rw [lookup_eq]; simp [hpc, hsg']
    refine ⟨⟨rp.reverse, m⟩, a', _, sg', L.bt, L.catches, cb, cl, hseq, hlk, ht', hcl, ?_⟩
    have key : (labelsRev body b.seq.reverse).getD (j + 1 + l.toNat) .invalid =
        resolveT (labels body rp.reverse) (catchLabel cl) := by
      rw [labelsRev_getD_drop body (j + 1) _ l.toNat (by omega), hd1]
      simp [resolveT, labels, hcle, Idx.toNat]
    split <;> simpa [labels] using key

end Silmaril.Wasm.Cfg.Proofs.Machine

/-! ## Region runs keep the frame's module -/

namespace Silmaril.Wasm.Cfg.Proofs.Machine

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **A region run keeps the frame's module instance** (only locals change), so block types
resolve the same way all along a run. -/
theorem run_module {s s' : Store H} {f f' : Frame} {vs : List Val} {code : List Admin}
    {o : Out} (h : Run P host s f vs code s' f' o) : f'.module = f.module := by
  induction h with
  | simple _ h₁ _ ih => exact ih.trans (Steps.frame_module h₁)
  | simpleTrap _ h₁ => exact Steps.frame_module h₁
  | call _ _ _ hcall => exact hcall.elim
  | callTrap _ _ _ hcall => exact hcall.elim
  | callThrow _ _ _ hcall => exact hcall.elim
  | _ => simp_all

end Silmaril.Wasm.Cfg.Proofs.Machine
