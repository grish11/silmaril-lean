module

public import Silmaril.Wasm.Cfg.Machine.Defs

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
