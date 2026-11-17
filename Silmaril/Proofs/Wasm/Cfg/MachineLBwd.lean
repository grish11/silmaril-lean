module

public import Silmaril.Proofs.Wasm.Cfg.MachineLFwd

@[expose] public section

/-!
# The logged machine against the logged relation: the converse (H2, proofs)

Continuation passing over the native derivation. `MEnds body Fin st l`: the machine runs from
`st` with the log `l` to an end (a sink, or a pending tail call) standing for a native result
satisfying `Fin`. `ExitE`: what the machine must do once a sequence ends with a native outcome.
-/

namespace Silmaril.Wasm.Cfg.Proofs.MachineLBwd

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Abstract (EvalLXPS SCall)
open Silmaril.Wasm.Abstract.CallXP (POut)
open Silmaril.Wasm.Cfg.Region (Catches)
open Silmaril.Wasm.Cfg.Proofs.Machine (restAt_cons restAt_end restAt_zero seg_of_lookup lookup_eq)
open Silmaril.Wasm.Cfg.Proofs.MachineLFwd

variable {H : Type}

/-- **The machine finishes**: from `st`, with the log `l`, it runs to a sink, or to a block whose
straight-line code ends in a pending tail call, standing for a native result satisfying `Fin`. -/
def MEnds (body : Expr) (Fin : Store H × Frame × POut → Prop) (st : MState H)
    (l : List (SCall H)) : Prop :=
  ∃ (st' : MState H) (r : Store H × Frame × POut) (l₁ l₂ : List (SCall H)),
    MRunL body st l₁ st' ∧ l = l₁ ++ l₂ ∧ Fin r ∧
      ((st'.node.IsSink ∧ l₂ = [] ∧ EndRel st' r) ∨ TailL body st' l₂ r)

theorem mEnds_step {body : Expr} {Fin : Store H × Frame × POut → Prop} {st st' : MState H}
    {l₀ l : List (SCall H)} (hs : MStepL body st l₀ st') (h : MEnds body Fin st' l) :
    MEnds body Fin st (l₀ ++ l) := by
  obtain ⟨st'', r, l₁, l₂, hr, rfl, hF, hend⟩ := h
  exact ⟨st'', r, l₀ ++ l₁, l₂, .step hs hr, by simp, hF, hend⟩

/-- A sink standing for a native result satisfying `Fin` finishes. -/
theorem mEnds_sink {body : Expr} {Fin : Store H × Frame × POut → Prop} {st : MState H}
    {r : Store H × Frame × POut} (hs : st.node.IsSink) (hE : EndRel st r) (hF : Fin r) :
    MEnds body Fin st [] :=
  ⟨st, r, [], [], .refl _, rfl, hF, .inl ⟨hs, rfl, hE⟩⟩

/-- **What the machine must do once the sequence at `p` ends with the native outcome `r`**, under
the frames `ls`, the rest of the log being `l'`: falling through, finish from the sequence's
continuation; a pending tail call, nothing (`l' = []`, `Fin r`); any other outcome, finish from
from a target `DispL` gives it. -/
def ExitE (body : Expr) (Fin : Store H × Frame × POut → Prop) (p : List SeqStep)
    (ls : List LFrame) (r : Store H × Frame × POut) (l' : List (SCall H)) : Prop :=
  match r.2.2 with
  | .flow (.normal ws) => ∃ st, gotoN (contRev body p.reverse) p.length ls ws.reverse r.1 r.2.1 =
      some st ∧ MEnds body Fin st l'
  | .tail .. => l' = [] ∧ Fin r
  | _ => ∃ st, DispL body ⟨p, 0⟩ ls r st ∧ MEnds body Fin st l'

/-- `DispL` on an abrupt outcome does not depend on the block's position. -/
theorem dispL_idx {body : Expr} {b : BlockId} {ls : List LFrame} {r : Store H × Frame × POut}
    {st : MState H} (hn : ¬ r.2.2.IsNormal) (hd : DispL body b ls r st) :
    DispL body ⟨b.seq, 0⟩ ls r st := by
  cases hd with
  | next => exact absurd trivial hn
  | br hL hg => exact .br hL (by simpa [branchN] using hg)
  | brOut hk => exact .brOut hk
  | ret => exact .ret
  | trap => exact .trap
  | raise hT => exact .raise hT
  | catch_ hpass hL hT hc hL' hg => exact .catch_ hpass hL hT hc hL' (by simpa [branchN] using hg)
  | catchOut hpass hL hT hc hout => exact .catchOut hpass hL hT hc hout

theorem dispL_idx' {body : Expr} {b : BlockId} {ls : List LFrame} {r : Store H × Frame × POut}
    {st : MState H} (hn : ¬ r.2.2.IsNormal) (hd : DispL body ⟨b.seq, 0⟩ ls r st) :
    DispL body b ls r st := by
  cases hd with
  | next => exact absurd trivial hn
  | br hL hg => exact .br hL (by simpa [branchN] using hg)
  | brOut hk => exact .brOut hk
  | ret => exact .ret
  | trap => exact .trap
  | raise hT => exact .raise hT
  | catch_ hpass hL hT hc hL' hg => exact .catch_ hpass hL hT hc hL' (by simpa [branchN] using hg)
  | catchOut hpass hL hT hc hout => exact .catchOut hpass hL hT hc hout

/-- **A block's straight-line code ran, ending abruptly or in a pending tail call**: the machine
finishes from the block. -/
theorem block_abrupt {body : Expr} {Fin : Store H × Frame × POut → Prop} {b : BlockId}
    {sg : Segment} {stk : List Val} {ls : List LFrame} {s : Store H} {f : Frame}
    {l l' : List (SCall H)} {r : Store H × Frame × POut} (hb : lookup body b = some sg)
    (ht : ∀ i, sg.term = some i → ¬ Instr.IsStruct i)
    (hr : EvalLXPS s f stk.reverse (liftInstrs (MachineL.codeOf sg)) l r)
    (hn : ¬ r.2.2.IsNormal) (hx : ExitE body Fin b.seq ls r l') :
    MEnds body Fin ⟨.block b, stk, ls, s, f⟩ (l ++ l') := by
  obtain ⟨s₁, f₁, o⟩ := r
  unfold ExitE at hx
  rcases o with fl | ⟨fa, args, n⟩
  · cases fl with
    | normal => exact absurd trivial hn
    | _ =>
      obtain ⟨st, hd, hE⟩ := hx
      exact mEnds_step (.run hb ht hr (dispL_idx' hn hd)) hE
  · obtain ⟨rfl, hF⟩ := hx
    exact ⟨_, _, [], l, .refl _, by simp, hF, .inr (.tail hb ht hr)⟩

end Silmaril.Wasm.Cfg.Proofs.MachineLBwd
