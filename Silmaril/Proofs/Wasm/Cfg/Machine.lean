module

public import Silmaril.Wasm.Cfg.Machine.Defs
public import Silmaril.Wasm.Cfg.Block.Thms
public import Silmaril.Proofs.Wasm.Cfg.Region

@[expose] public section

namespace Silmaril.Wasm.Cfg.Proofs.Machine

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics

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
  | @enter _ sg _ _ _ _ _ _ _ _ _ i a c bt _ _ _ _ hb ht harm hkind =>
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

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem mstep_from_block {body : Expr} {st st' : MState H} (h : MStep P host body st st') :
    ∃ b, st.node = .block b := by
  cases h <;> exact ⟨_, rfl⟩

end Silmaril.Wasm.Cfg.Proofs.Machine

namespace Silmaril.Wasm.Cfg.Proofs.Machine

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
