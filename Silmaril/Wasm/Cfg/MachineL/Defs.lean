module

public import Silmaril.Wasm.Cfg.Machine.Defs
public import Silmaril.Wasm.Abstract.HostClosingS.Defs

/-!
# The logged block-CFG machine (H1, definitions)

The block-CFG machine `Cfg.Machine.MStepC` is unlabelled: its simple steps are Core runs and its
calls are answered by a stateless oracle, so a run's host-event log cannot be read off it. The
logged machine runs the **same control-flow graph with the same control rules**, but runs each
block's straight-line code by the canonical store-retaining logged relation
`Abstract.EvalLXPS`. There every call (`call`, resolved `call_indirect`, `call_ref`; Wasm and host
callees alike) is an **open call recorded in the log** with an arbitrary answer: values, an
exception raised at the call, or a callee trap with the store it left (`SCall`).

* A block whose terminator is not structured (none, a branch, `return`, `unreachable`, a throw,
  a tail call) runs its segment and terminator, `codeOf sg = sg.body ++ sg.term.toList`, as one
  straight-line `EvalLXPS` run, on the reversed machine stack (machine stacks are bottom first,
  native ones top first). The machine then moves on the native outcome (`DispL`), with the
  targets and run-time checks of `MStepC`: falling through (`goto` the next position), a branch to
  label `k` (`brVals`, `topVals`, loops re-entered), the function label and `return` (`exit` with
  the whole frame stack), a trap keeping its store, and an exception (uncaught: `raise`; caught
  by the first matching `try_table` frame: a branch from outside it, `Catches`).
* A block ending in a structured instruction (`block`, `loop`, `if`, `try_table`) runs its
  segment, then enters the arm (`MStepL.enter`, `StructKind`, `CondArm`), pushing a label
  frame as `MStepC.enter` does; a segment ending abruptly (a callee trap, an exception from a
  call) is dispatched (`MStepL.abort`).
* A pending tail call is an **end** of the body, not a step (`TailL`): the open module makes the
  call when the function's frame is left, outside every handler, as `EvalLXPS`'s `tail` rule
  leaves it pending through labels and handlers.
* `MRunL body st l st'`: finitely many logged steps, their logs concatenated in order.

No block evaluates nested structured code natively: every block step runs straight-line code.

Not yet here (H1 proofs, H2, H3; `docs/projects/wasm-cfg.md`): the forward theorem against
`EvalLXPS` on bodies, the projection to `MStepC`, the converse, pending calls, divergence and
productive streams, and the recursive closure.
-/

@[expose] public section

namespace Silmaril.Wasm.Cfg.MachineL

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Abstract (EvalLXPS SCall)
open Silmaril.Wasm.Abstract.CallXP (POut)
open Silmaril.Wasm.Cfg.Region (Catches)

variable {H : Type}

/-- The structured instructions: their block ends by entering an arm. -/
def Instr.IsStruct (i : Instr) : Prop := ∃ bt loop tryT cs, StructKind i bt loop tryT cs

/-- **The straight-line code of a block**: its segment and its terminator, when that is not
structured. -/
def codeOf (sg : Segment) : List Instr := sg.body ++ sg.term.toList

/-- **Where a block's straight-line code leads**, from its native outcome `r` (store, frame,
outcome), under the label frames `ls`: `MStepC`'s targets and run-time checks. -/
inductive DispL (body : Expr) (b : BlockId) (ls : List LFrame) :
    Store H × Frame × POut → MState H → Prop where
  /-- Falling through: the next position of the sequence. -/
  | next {s : Store H} {f : Frame} {ws : List Val} :
      DispL body b ls (s, f, .flow (.normal ws))
        (goto (entry body b.seq (b.idx + 1)) b.seq.length ls ws.reverse s f)
  /-- A branch to an enclosing label `k`: re-enter a loop or leave the label's sequence, with the
  values `brVals` collects, as `MStepC.br`. -/
  | br {s : Store H} {f : Frame} {ws : List Val} {k : Nat} {L : LFrame}
      (hL : ls[k]? = some L) (harity : L.arity ≤ (brVals k ls ws.reverse).length)
      (hlbt : L.loop = true → ∃ t₁ t₂, f.module.blockType? L.bt = some (t₁, t₂) ∧
        t₁.length = L.arity) :
      DispL body b ls (s, f, .flow (.brk k ws))
        (if L.loop then
          goto ((labels body b.seq).getD k .invalid) (b.seq.length - k)
            (L :: ls.drop (k + 1)) (topVals L.arity (brVals k ls ws.reverse)) s f
        else
          goto ((labels body b.seq).getD k .invalid) (b.seq.length - (k + 1))
            (ls.drop (k + 1)) (L.outer ++ topVals L.arity (brVals k ls ws.reverse)) s f)
  /-- A branch to the function label: `exit` with the whole frame stack. -/
  | brOut {s : Store H} {f : Frame} {ws : List Val} {k : Nat} (hk : k = ls.length) :
      DispL body b ls (s, f, .flow (.brk k ws)) ⟨.exit, brVals ls.length ls ws.reverse, [], s, f⟩
  /-- `return`: `exit` with the whole frame stack. -/
  | ret {s : Store H} {f : Frame} {ws : List Val} :
      DispL body b ls (s, f, .flow (.ret ws)) ⟨.exit, brVals ls.length ls ws.reverse, [], s, f⟩
  /-- A trap, keeping its store. -/
  | trap {s : Store H} {f : Frame} :
      DispL body b ls (s, f, .flow .trap) ⟨.trap, [], [], s, f⟩
  /-- An exception no enclosing `try_table` frame catches. -/
  | raise {s : Store H} {f : Frame} {a : Nat}
      (hT : ∀ (k : Nat) (L : LFrame), ls[k]? = some L → L.tryT = true →
        Catches s f a L.catches none) :
      DispL body b ls (s, f, .flow (.throw a)) ⟨.raise, [.ref (.exn a)], [], s, f⟩
  /-- An exception caught by the `try_table` frame `j` with the clause branching to `l`, an
  enclosing label: a branch from outside the `try_table`, as `MStepC.catch_`. -/
  | catch_ {s : Store H} {f : Frame} {a j : Nat} {us : List Val} {L L' : LFrame} {l : LabelIdx}
      (hpass : ∀ (k : Nat) (L : LFrame), k < j → ls[k]? = some L → L.tryT = true →
        Catches s f a L.catches none)
      (hL : ls[j]? = some L) (hT : L.tryT = true) (hc : Catches s f a L.catches (some (us, l)))
      (hL' : ls[j + 1 + l.toNat]? = some L')
      (harity : L'.arity ≤ (brVals l.toNat (ls.drop (j + 1)) (L.outer ++ us)).length)
      (hlbt : L'.loop = true → ∃ t₁ t₂, f.module.blockType? L'.bt = some (t₁, t₂) ∧
        t₁.length = L'.arity) :
      DispL body b ls (s, f, .flow (.throw a))
        (if L'.loop then
          goto ((labels body b.seq).getD (j + 1 + l.toNat) .invalid)
            (b.seq.length - (j + 1 + l.toNat)) (L' :: ls.drop (j + 1 + l.toNat + 1))
            (topVals L'.arity (brVals l.toNat (ls.drop (j + 1)) (L.outer ++ us))) s f
        else
          goto ((labels body b.seq).getD (j + 1 + l.toNat) .invalid)
            (b.seq.length - (j + 1 + l.toNat + 1)) (ls.drop (j + 1 + l.toNat + 1))
            (L'.outer ++ topVals L'.arity (brVals l.toNat (ls.drop (j + 1)) (L.outer ++ us))) s f)
  /-- An exception caught with a clause branching to the function label: `exit`, as
  `MStepC.catchOut`. -/
  | catchOut {s : Store H} {f : Frame} {a j : Nat} {us : List Val} {L : LFrame} {l : LabelIdx}
      (hpass : ∀ (k : Nat) (L : LFrame), k < j → ls[k]? = some L → L.tryT = true →
        Catches s f a L.catches none)
      (hL : ls[j]? = some L) (hT : L.tryT = true) (hc : Catches s f a L.catches (some (us, l)))
      (hout : j + 1 + l.toNat = ls.length) :
      DispL body b ls (s, f, .flow (.throw a))
        ⟨.exit, brVals l.toNat (ls.drop (j + 1)) (L.outer ++ us), [], s, f⟩

/-- **One logged step of the block-CFG machine**, with the log of its open calls. -/
inductive MStepL (body : Expr) : MState H → List (SCall H) → MState H → Prop where
  /-- A block not ending in a structured instruction: its straight-line code, then `DispL`. -/
  | run {b : BlockId} {sg : Segment} {stk : List Val} {ls : List LFrame} {s : Store H}
      {f : Frame} {l : List (SCall H)} {r : Store H × Frame × POut} {st' : MState H}
      (hb : lookup body b = some sg) (ht : ∀ i, sg.term = some i → ¬ Instr.IsStruct i)
      (hr : EvalLXPS s f stk.reverse (liftInstrs (codeOf sg)) l r) (hd : DispL body b ls r st') :
      MStepL body ⟨.block b, stk, ls, s, f⟩ l st'
  /-- A block ending in a structured instruction whose segment ends abruptly. -/
  | abort {b : BlockId} {sg : Segment} {stk : List Val} {ls : List LFrame} {s : Store H}
      {f : Frame} {l : List (SCall H)} {r : Store H × Frame × POut} {st' : MState H}
      (hb : lookup body b = some sg) (hr : EvalLXPS s f stk.reverse (liftInstrs sg.body) l r)
      (hn : ¬ r.2.2.IsNormal) (hd : DispL body b ls r st') :
      MStepL body ⟨.block b, stk, ls, s, f⟩ l st'
  /-- Entering arm `a` of a structured terminator after the segment, as `MStepC.enter`. -/
  | enter {b : BlockId} {sg : Segment} {stk stk₁ ws us : List Val} {ls : List LFrame}
      {s s₁ : Store H} {f f₁ : Frame} {i : Instr} {a : Nat} {c : List Instr} {bt : BlockType}
      {t₁ t₂ : List Validation.CValType} {loop tryT : Bool} {cs : List Catch} {l : List (SCall H)}
      (hb : lookup body b = some sg) (ht : sg.term = some i) (harm : armOf i a = some c)
      (hkind : StructKind i bt loop tryT cs)
      (hr : EvalLXPS s f stk.reverse (liftInstrs sg.body) l (s₁, f₁, .flow (.normal stk₁)))
      (hcond : CondArm i stk₁.reverse a ws us)
      (hbt : f₁.module.blockType? bt = some (t₁, t₂)) (hm : us.length = t₁.length) :
      MStepL body ⟨.block b, stk, ls, s, f⟩ l
        (goto (entry body (b.seq ++ [(b.idx, a)]) 0) (b.seq.length + 1)
          (⟨labelArity loop t₁ t₂, ws, loop, tryT, cs, bt⟩ :: ls) us s₁ f₁)

/-- **A pending tail call ends the body**: a block's straight-line code ends in a pending tail
call (through every label and handler), which the function's frame makes. -/
inductive TailL (body : Expr) : MState H → List (SCall H) → Store H × Frame × POut → Prop where
  | tail {b : BlockId} {sg : Segment} {stk : List Val} {ls : List LFrame} {s s₁ : Store H}
      {f f₁ : Frame} {l : List (SCall H)} {fa n : Nat} {args : List Val}
      (hb : lookup body b = some sg) (ht : ∀ i, sg.term = some i → ¬ Instr.IsStruct i)
      (hr : EvalLXPS s f stk.reverse (liftInstrs (codeOf sg)) l (s₁, f₁, .tail fa args n)) :
      TailL body ⟨.block b, stk, ls, s, f⟩ l (s₁, f₁, .tail fa args n)

/-- **Logged runs**: finitely many logged steps, their logs in order. -/
inductive MRunL (body : Expr) : MState H → List (SCall H) → MState H → Prop where
  | refl (st : MState H) : MRunL body st [] st
  | step {st st₁ st₂ : MState H} {l₁ l₂ : List (SCall H)} (h : MStepL body st l₁ st₁)
      (hr : MRunL body st₁ l₂ st₂) : MRunL body st (l₁ ++ l₂) st₂

end Silmaril.Wasm.Cfg.MachineL
