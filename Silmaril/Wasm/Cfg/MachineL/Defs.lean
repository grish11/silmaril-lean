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
  native ones top first). The machine then moves on the native outcome (`DispL`) to the CFG
  targets of `MStepC`: falling through (the next position, leaving finished sequences), a branch
  to label `k` (a loop re-entered), the function label and `return` (`exit`), a trap keeping its
  store, and an exception (uncaught: `raise`; caught by the first matching `try_table` frame: a
  branch from outside it, `Catches`).

**Stack conventions: native, not Core.** At frame boundaries `MStepL` follows `EvalLXPS`: leaving
an arm keeps the top `nr` values over the frame's outer values (`popN`, `gotoN`); a branch keeps
the top `arity` values of the branch-site stack over the target's outer values (`branchN`), with
no values of the frames in between; `return` and a branch out of the function exit with the stack
at the branch; there are no run-time arity checks. `MStepC` follows Core (`popL` keeps the whole
stack, `brVals` collects the left frames' values, arity checks). The two agree on typed code; on
untyped code they differ, as native and Core semantics do, and no untyped correspondence between
`MStepL` and `MStepC` is claimed.
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

/-- **Leave `k` sequences, native conventions**: each label frame `L` keeps the top `nr` values of
the stack over its outer values, `nr` the result arity of its block type (`Binaryen.arity`), as
`EvalLXPS`'s `blockOk`, `loopOk`, `ifOk`, `tryOk` continue on `vs.take nr ++ outer`. (`MStepC`'s
`popL` keeps the whole stack, as Core's `label-vals`; the two agree on typed code.) -/
def popN (f : Frame) : Nat → List LFrame → List Val → Option (List LFrame × List Val)
  | 0, ls, stk => some (ls, stk)
  | _ + 1, [], _ => none
  | k + 1, L :: ls, stk =>
    (Binaryen.arity f L.bt).bind fun a => popN f k ls (L.outer ++ topVals a.2 stk)

/-- **Move to `t` from depth `d`, native conventions** (`popN`); `none` if a left frame's block
type has no arity. -/
def gotoN (t : Target) (d : Nat) (ls : List LFrame) (stk : List Val) (s : Store H) (f : Frame) :
    Option (MState H) :=
  (popN f (d - depthT t) ls stk).map fun p => ⟨t, p.2, p.1, s, f⟩

/-- **Branch to label `k` of the frames `ls` from block `b`, native conventions**, with the
branch-site stack `N` **top first** (as `EvalLXPS` carries it) and the arities `(np, nr)` of the
label's block type (`Binaryen.arity`):

* a `loop` is re-entered as `EvalLXPS`'s `loopBack` re-runs it: on `R = N.take np ++ outer` (top
  first), its parameters are the top `np` values of `R` and its frame's outer values the rest
  (when `N` holds at least `np` values, the parameters are the top `np` of `N` and the outer values
  are unchanged);
* any other label leaves its sequence (`gotoN`) with the top `nr` values of `N` over its outer
  values (`blockOk`'s `vs.take nr ++ outer`).

No values of the frames in between are collected (`EvalLXPS`'s `blockBrk` passes a branch's values
unchanged; `MStepC`'s `brVals` collects them, as Core does; they agree on typed code). -/
def branchN (body : Expr) (b : BlockId) (ls : List LFrame) (k : Nat) (L : LFrame) (N : List Val)
    (s : Store H) (f : Frame) : Option (MState H) :=
  (Binaryen.arity f L.bt).bind fun a =>
    if L.loop then
      let R := N.take a.1 ++ L.outer.reverse
      gotoN ((labels body b.seq).getD k .invalid) (b.seq.length - k)
        ({ L with outer := (R.drop a.1).reverse } :: ls.drop (k + 1)) (R.take a.1).reverse s f
    else
      gotoN ((labels body b.seq).getD k .invalid) (b.seq.length - (k + 1)) (ls.drop (k + 1))
        (L.outer ++ (N.take a.2).reverse) s f

/-- **Which arm of a structured instruction runs, natively**, on the native stack `V` (top first)
after its segment: an `if` pops its condition `cv` (`truthy`) and runs arm `0` when it is
nonzero, `1` otherwise; the others run arm `0`. `V'` is the stack left. -/
inductive ArmSel : Instr → List Val → Nat → List Val → Prop where
  | plain {i : Instr} {V : List Val} (hi : ∀ bt t e, i ≠ .if_ bt t e) : ArmSel i V 0 V
  | cond {bt : BlockType} {t e : List Instr} {cv : Val} {V : List Val} {b : Bool}
      (hb : truthy cv = some b) : ArmSel (.if_ bt t e) (cv :: V) (if b then 0 else 1) V

/-- **Where a block's straight-line code leads**, from its native outcome `r` (store, frame,
outcome; native stacks top first), under the label frames `ls`: the CFG targets of `MStepC`, with
the **native stack conventions** of `EvalLXPS`. -/
inductive DispL (body : Expr) (b : BlockId) (ls : List LFrame) :
    Store H × Frame × POut → MState H → Prop where
  /-- Falling through: the next position of the sequence, leaving finished sequences
  natively. -/
  | next {s : Store H} {f : Frame} {ws : List Val} {st' : MState H}
      (hg : gotoN (entry body b.seq (b.idx + 1)) b.seq.length ls ws.reverse s f = some st') :
      DispL body b ls (s, f, .flow (.normal ws)) st'
  /-- A branch to an enclosing label `k` (`branchN`). -/
  | br {s : Store H} {f : Frame} {ws : List Val} {k : Nat} {L : LFrame} {st' : MState H}
      (hL : ls[k]? = some L) (hg : branchN body b ls k L ws s f = some st') :
      DispL body b ls (s, f, .flow (.brk k ws)) st'
  /-- A branch to the function label: `exit` with the branch-site stack. -/
  | brOut {s : Store H} {f : Frame} {ws : List Val} {k : Nat} (hk : k = ls.length) :
      DispL body b ls (s, f, .flow (.brk k ws)) ⟨.exit, ws.reverse, [], s, f⟩
  /-- `return`: `exit` with the stack at the `return`. -/
  | ret {s : Store H} {f : Frame} {ws : List Val} :
      DispL body b ls (s, f, .flow (.ret ws)) ⟨.exit, ws.reverse, [], s, f⟩
  /-- A trap, keeping its store. -/
  | trap {s : Store H} {f : Frame} :
      DispL body b ls (s, f, .flow .trap) ⟨.trap, [], [], s, f⟩
  /-- An exception no enclosing `try_table` frame catches. -/
  | raise {s : Store H} {f : Frame} {a : Nat}
      (hT : ∀ (k : Nat) (L : LFrame), ls[k]? = some L → L.tryT = true →
        Catches s f a L.catches none) :
      DispL body b ls (s, f, .flow (.throw a)) ⟨.raise, [.ref (.exn a)], [], s, f⟩
  /-- An exception caught by the `try_table` frame `j` with the clause branching to `l`: a branch
  from outside the `try_table` with the caught values over its outer values (`EvalLXPS`'s
  `tryCatch`), to label `j + 1 + l` (`branchN`). -/
  | catch_ {s : Store H} {f : Frame} {a j : Nat} {us : List Val} {L L' : LFrame} {l : LabelIdx}
      {st' : MState H}
      (hpass : ∀ (k : Nat) (L : LFrame), k < j → ls[k]? = some L → L.tryT = true →
        Catches s f a L.catches none)
      (hL : ls[j]? = some L) (hT : L.tryT = true) (hc : Catches s f a L.catches (some (us, l)))
      (hL' : ls[j + 1 + l.toNat]? = some L')
      (hg : branchN body b ls (j + 1 + l.toNat) L' (us.reverse ++ L.outer.reverse) s f = some st') :
      DispL body b ls (s, f, .flow (.throw a)) st'
  /-- An exception caught with a clause branching to the function label: `exit` with the caught
  values over the `try_table`'s outer values. -/
  | catchOut {s : Store H} {f : Frame} {a j : Nat} {us : List Val} {L : LFrame} {l : LabelIdx}
      (hpass : ∀ (k : Nat) (L : LFrame), k < j → ls[k]? = some L → L.tryT = true →
        Catches s f a L.catches none)
      (hL : ls[j]? = some L) (hT : L.tryT = true) (hc : Catches s f a L.catches (some (us, l)))
      (hout : j + 1 + l.toNat = ls.length) :
      DispL body b ls (s, f, .flow (.throw a)) ⟨.exit, L.outer ++ us, [], s, f⟩

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
  /-- Entering arm `a` of a structured terminator after the segment, natively: the arm runs on
  the top `np` values of the stack left (`ArmSel`), the frame keeping the rest as its outer values
  (`EvalLXPS`'s `stk.take np`, `stk.drop np`); an empty arm continues at once, leaving its sequence
  natively. -/
  | enter {b : BlockId} {sg : Segment} {stk : List Val} {V V' : List Val} {ls : List LFrame}
      {s s₁ : Store H} {f f₁ : Frame} {i : Instr} {a : Nat} {c : List Instr} {bt : BlockType}
      {np nr : Nat} {loop tryT : Bool} {cs : List Catch} {l : List (SCall H)} {st' : MState H}
      (hb : lookup body b = some sg) (ht : sg.term = some i) (harm : armOf i a = some c)
      (hkind : StructKind i bt loop tryT cs)
      (hr : EvalLXPS s f stk.reverse (liftInstrs sg.body) l (s₁, f₁, .flow (.normal V)))
      (hsel : ArmSel i V a V') (har : Binaryen.arity f₁ bt = some (np, nr))
      (hg : gotoN (entry body (b.seq ++ [(b.idx, a)]) 0) (b.seq.length + 1)
          (⟨if loop then np else nr, (V'.drop np).reverse, loop, tryT, cs, bt⟩ :: ls)
          (V'.take np).reverse s₁ f₁ = some st') :
      MStepL body ⟨.block b, stk, ls, s, f⟩ l st'

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

/-- **What a sink state stands for natively**: `exit` a flow returning its stack (top first),
`trap` a trap, `raise` the exception on its stack, all in its store and frame. -/
def EndRel (st : MState H) (r : Store H × Frame × POut) : Prop :=
  match st.node with
  | .exit => ∃ fl, r = (st.store, st.frame, .flow fl) ∧ fl.retVals = some st.stk.reverse
  | .trap => r = (st.store, st.frame, .flow .trap)
  | .raise => ∃ a, st.stk = [.ref (.exn a)] ∧ r = (st.store, st.frame, .flow (.throw a))
  | _ => False

end Silmaril.Wasm.Cfg.MachineL
