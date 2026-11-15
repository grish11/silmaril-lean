module

public import Silmaril.Wasm.Cfg.BlockCfg.Defs
public import Silmaril.Wasm.Cfg.Region.Defs

@[expose] public section

/-!
# An executable machine over the extracted basic-block CFG

`MStep P host body` steps a machine whose control state is a node of the extracted block CFG
(`Cfg.Target`, blocks named by `BlockId` and found by `lookup`). Each step runs one basic block
(`Segment`): its simple body by the region semantics (`Region.Run`, call-free, straight-line),
then its terminator. The terminator moves to a node computed by the same functions the CFG
uses (`entry`, `labels`, `resolveT`), so that every machine step follows a `Cfg.Edge`
(`Machine/Thms.lean`). This is a graph fact only. Agreement of machine runs with `Region.Run`
and Core 3.0 is a separate obligation and is not proved here.

The data state is the value stack, the store, the frame and a stack of label frames
(`LFrame`), one per enclosing structured instruction: its branch arity, the values held
outside it, whether it is a `loop`, and its `catch` clauses. Leaving sequences pops label
frames as Core's `label-vals` does (`popL`). Exceptions, returns and traps go to the sink nodes
`raise`, `exit` and `trap`. Catching (handler resolution against `catches`), `br_table`,
`br_on_*` and calls are not modelled yet.
-/

namespace Silmaril.Wasm.Cfg.Machine

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
open Silmaril.Wasm.Cfg.Region

variable {H : Type}

/-- A label frame: one enclosing structured instruction. -/
structure LFrame where
  /-- Values a branch to this label keeps. -/
  arity : Nat
  /-- The stack outside the structured instruction. -/
  outer : List Val
  /-- A `loop`: a branch re-enters it. -/
  loop : Bool
  /-- A `try_table`: its label sits inside a `HANDLER` (even with no clauses). -/
  tryT : Bool
  /-- The `catch` clauses of a `try_table` (empty otherwise). -/
  catches : List Catch
  deriving Repr

/-- A machine state. -/
structure MState (H : Type) where
  node : Target
  stk : List Val
  lbls : List LFrame
  store : Store H
  frame : Frame

/-- Leave `k` sequences: each label frame's outer values go under the stack (`label-vals`). -/
def popL : Nat → List LFrame → List Val → List LFrame × List Val
  | 0, ls, stk => (ls, stk)
  | _ + 1, [], stk => ([], stk)
  | k + 1, l :: ls, stk => popL k ls (l.outer ++ stk)

/-- The nesting depth of a node: the length of its sequence path (sinks are at depth `0`). -/
def depthT : Target → Nat
  | .block b => b.seq.length
  | _ => 0

/-- Move to `t` from a context of depth `d`, leaving the sequences in between. -/
def goto (t : Target) (d : Nat) (ls : List LFrame) (stk : List Val) (s : Store H) (f : Frame) :
    MState H :=
  let p := popL (d - depthT t) ls stk
  ⟨t, p.2, p.1, s, f⟩

/-- The block-type arity of a structured instruction's label: results for `block`, `if` and
`try_table`, parameters for `loop`. -/
def labelArity (loop : Bool) (t₁ t₂ : List CValType) : Nat := if loop then t₁.length else t₂.length

/-- The structured terminators, with block type, `loop` flag and `catch` clauses. -/
inductive StructKind : Instr → BlockType → Bool → Bool → List Catch → Prop where
  | block {bt : BlockType} {b : List Instr} : StructKind (.block bt b) bt false false []
  | loop {bt : BlockType} {b : List Instr} : StructKind (.loop bt b) bt true false []
  | if_ {bt : BlockType} {t e : List Instr} : StructKind (.if_ bt t e) bt false false []
  | tryTable {bt : BlockType} {cs : List Catch} {b : List Instr} :
      StructKind (.tryTable bt cs b) bt false true cs

/-- Which arm of a structured terminator runs, and the stack split into the values outside it
(`ws`) and its parameters (`us`): `if` pops its `i32` condition first. -/
inductive CondArm : Instr → List Val → Nat → List Val → List Val → Prop where
  | plain {i : Instr} {ws us : List Val} (hi : ∀ bt t e, i ≠ .if_ bt t e) :
      CondArm i (ws ++ us) 0 ws us
  | ifTrue {bt : BlockType} {t e : List Instr} {ws us : List Val} {k : BitVec 32} (hk : k ≠ 0) :
      CondArm (.if_ bt t e) (ws ++ us ++ [.i32 k]) 0 ws us
  | ifFalse {bt : BlockType} {t e : List Instr} {ws us : List Val} :
      CondArm (.if_ bt t e) (ws ++ us ++ [.i32 0]) 1 ws us

/-- `throw` and `throw_ref`. -/
def _root_.Silmaril.Wasm.Instr.IsThrow : Instr → Prop
  | .throw _ | .throwRef => True
  | _ => False

/-- **One block step.** From block `b`, run its simple body (`Region.Run`, to values), then its
terminator. -/
inductive MStep (P : Profile) (host : HostSemantics H) (body : Expr) :
    MState H → MState H → Prop where
  /-- No terminator: fall through to the next position of the sequence. -/
  | fall {b : BlockId} {sg : Segment} {stk stk₁ : List Val} {ls : List LFrame} {s s₁ : Store H}
      {f f₁ : Frame} (hb : lookup body b = some sg) (ht : sg.term = none)
      (hr : Run P host s f stk (expression sg.body) s₁ f₁ (.normal stk₁)) :
      MStep P host body ⟨.block b, stk, ls, s, f⟩
        (goto (entry body b.seq (b.idx + 1)) b.seq.length ls stk₁ s₁ f₁)
  /-- `br l`: keep the label's top values; re-enter a loop, or leave the label's sequence. -/
  | br {b : BlockId} {sg : Segment} {stk stk₁ : List Val} {ls : List LFrame} {s s₁ : Store H}
      {f f₁ : Frame} {l : LabelIdx} {L : LFrame} (hb : lookup body b = some sg)
      (ht : sg.term = some (.br l))
      (hr : Run P host s f stk (expression sg.body) s₁ f₁ (.normal stk₁))
      (hL : ls[l.toNat]? = some L) :
      MStep P host body ⟨.block b, stk, ls, s, f⟩
        (if L.loop then
          goto (resolveT (labels body b.seq) l) (b.seq.length - l.toNat)
            (L :: ls.drop (l.toNat + 1)) (stk₁.drop (stk₁.length - L.arity)) s₁ f₁
        else
          goto (resolveT (labels body b.seq) l) (b.seq.length - (l.toNat + 1))
            (ls.drop (l.toNat + 1)) (L.outer ++ stk₁.drop (stk₁.length - L.arity)) s₁ f₁)
  /-- `br_if l` with a nonzero condition branches like `br l`. -/
  | brIfTaken {b : BlockId} {sg : Segment} {stk stk₁ : List Val} {ls : List LFrame}
      {s s₁ : Store H} {f f₁ : Frame} {l : LabelIdx} {L : LFrame} {k : BitVec 32}
      (hb : lookup body b = some sg) (ht : sg.term = some (.brIf l))
      (hr : Run P host s f stk (expression sg.body) s₁ f₁ (.normal (stk₁ ++ [.i32 k])))
      (hk : k ≠ 0) (hL : ls[l.toNat]? = some L) :
      MStep P host body ⟨.block b, stk, ls, s, f⟩
        (if L.loop then
          goto (resolveT (labels body b.seq) l) (b.seq.length - l.toNat)
            (L :: ls.drop (l.toNat + 1)) (stk₁.drop (stk₁.length - L.arity)) s₁ f₁
        else
          goto (resolveT (labels body b.seq) l) (b.seq.length - (l.toNat + 1))
            (ls.drop (l.toNat + 1)) (L.outer ++ stk₁.drop (stk₁.length - L.arity)) s₁ f₁)
  /-- `br_if l` with a zero condition falls through. -/
  | brIfNot {b : BlockId} {sg : Segment} {stk stk₁ : List Val} {ls : List LFrame}
      {s s₁ : Store H} {f f₁ : Frame} {l : LabelIdx} (hb : lookup body b = some sg)
      (ht : sg.term = some (.brIf l))
      (hr : Run P host s f stk (expression sg.body) s₁ f₁ (.normal (stk₁ ++ [.i32 0]))) :
      MStep P host body ⟨.block b, stk, ls, s, f⟩
        (goto (entry body b.seq (b.idx + 1)) b.seq.length ls stk₁ s₁ f₁)
  /-- Entering arm `a` of a structured terminator (`block`, `loop`, `if` with its condition,
  `try_table`): push its label frame on the parameters. -/
  | enter {b : BlockId} {sg : Segment} {stk stk₁ ws us : List Val} {ls : List LFrame}
      {s s₁ : Store H} {f f₁ : Frame} {i : Instr} {a : Nat} {c : List Instr} {bt : BlockType}
      {t₁ t₂ : List CValType} {loop tryT : Bool} {cs : List Catch}
      (hb : lookup body b = some sg) (ht : sg.term = some i) (harm : armOf i a = some c)
      (hkind : StructKind i bt loop tryT cs)
      (hr : Run P host s f stk (expression sg.body) s₁ f₁ (.normal stk₁))
      (hcond : CondArm i stk₁ a ws us)
      (hbt : f₁.module.blockType? bt = some (t₁, t₂)) (hm : us.length = t₁.length) :
      MStep P host body ⟨.block b, stk, ls, s, f⟩
        (goto (entry body (b.seq ++ [(b.idx, a)]) 0) (b.seq.length + 1)
          (⟨labelArity loop t₁ t₂, ws, loop, tryT, cs⟩ :: ls) us s₁ f₁)
  /-- `return` leaves the function. -/
  | ret {b : BlockId} {sg : Segment} {stk stk₁ : List Val} {ls : List LFrame} {s s₁ : Store H}
      {f f₁ : Frame} (hb : lookup body b = some sg) (ht : sg.term = some .return_)
      (hr : Run P host s f stk (expression sg.body) s₁ f₁ (.normal stk₁)) :
      MStep P host body ⟨.block b, stk, ls, s, f⟩ ⟨.exit, stk₁, [], s₁, f₁⟩
  /-- `unreachable`, or a trap in the block's body. -/
  | trap {b : BlockId} {sg : Segment} {stk : List Val} {ls : List LFrame} {s s₁ : Store H}
      {f f₁ : Frame} (hb : lookup body b = some sg) (ht : sg.term = some .unreachable)
      (hr : ∃ stk₁, Run P host s f stk (expression sg.body) s₁ f₁ (.normal stk₁)) :
      MStep P host body ⟨.block b, stk, ls, s, f⟩ ⟨.trap, [], [], s₁, f₁⟩
  /-- A trap in the block's straight-line body (an effect of one of its instructions). -/
  | bodyTrap {b : BlockId} {sg : Segment} {stk : List Val} {ls : List LFrame} {s s₁ : Store H}
      {f f₁ : Frame} (hb : lookup body b = some sg)
      (hr : Run P host s f stk (expression sg.body) s₁ f₁ .trap) :
      MStep P host body ⟨.block b, stk, ls, s, f⟩ ⟨.trap, [], [], s₁, f₁⟩
  /-- `throw` and `throw_ref`: the terminator runs (allocating the exception for `throw`) and
  the machine moves to the `raise` sink with the exception's address as its stack
  (`[ref (exn a)]`) and the store after the throw. Catching is not modelled yet. -/
  | raise {b : BlockId} {sg : Segment} {stk stk₁ : List Val} {ls : List LFrame}
      {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {i : Instr} {a : Nat} (hb : lookup body b = some sg)
      (ht : sg.term = some i) (hi : i.IsThrow)
      (hr : Run P host s f stk (expression sg.body) s₁ f₁ (.normal stk₁))
      (hth : Run P host s₁ f₁ stk₁ [.plain i] s₂ f₂ (.throw a)) :
      MStep P host body ⟨.block b, stk, ls, s, f⟩ ⟨.raise, [.ref (.exn a)], [], s₂, f₂⟩

end Silmaril.Wasm.Cfg.Machine

namespace Silmaril.Wasm.Cfg.Machine

/-- The nested sequence at sequence path `q` of `is`: follow each step's segment terminator and
arm, as `blockAt` does. -/
def seqAt : List Instr → List SeqStep → Option (List Instr)
  | is, [] => some is
  | is, (m, a) :: q => do
    let s ← (segment is)[m]?
    let t ← s.term
    let c ← armOf t a
    seqAt c q

/-- The instructions of sequence `c` from its block `i` on: what is left to run there. -/
def restAt (c : List Instr) (i : Nat) : List Instr := ((segment c).drop i).flatMap Segment.instrs

end Silmaril.Wasm.Cfg.Machine

namespace Silmaril.Wasm.Cfg.Machine

open Silmaril.Wasm.Execution.Core

/-! ## The label invariant: the region code a machine state stands for -/

/-- The region code of the context at reversed path `rp` with label frames `ls` (innermost
first) around inner code `inner`. Each frame becomes Core's `LABEL` (with the `loop` itself as
continuation for a loop), inside a `HANDLER` for a `try_table`, under its outer values and
before the rest of the parent sequence. `none` when path and frames do not match. -/
def wrap (body : Expr) : List SeqStep → List LFrame → List Admin → Option (List Admin)
  | [], [], inner => some inner
  | (m, _) :: rp, L :: ls, inner => do
    let pc ← seqAt body rp.reverse
    let sg ← (segment pc)[m]?
    let t ← sg.term
    let lab := Admin.label L.arity (if L.loop then [t] else []) inner
    let x := if L.tryT then Admin.handler L.arity L.catches [lab] else lab
    wrap body rp ls (vals L.outer ++ x :: expression (restAt pc (m + 1)))
  | _, _, _ => none

/-- **The region code a machine state at a block stands for**: its stack and the rest of its
sequence, wrapped by its label frames. -/
def codeAt (body : Expr) (b : BlockId) (stk : List Val) (ls : List LFrame) : Option (List Admin) :=
  do
    let c ← seqAt body b.seq
    wrap body b.seq.reverse ls (vals stk ++ expression (restAt c b.idx))

end Silmaril.Wasm.Cfg.Machine

namespace Silmaril.Wasm.Cfg.Machine

open Silmaril.Wasm.Execution.Core

/-- **The region code a machine state stands for**: `codeAt` at a block; the final values at
`exit` (with no label left); `[TRAP]` at `trap`; the thrown exception `throwing a` at `raise`,
whose stack holds its address `[ref (exn a)]`. -/
def codeOf (body : Expr) {H : Type} (st : MState H) : Option (List Admin) :=
  match st.node with
  | .block b => codeAt body b st.stk st.lbls
  | .exit => if st.lbls = [] then some (vals st.stk) else none
  | .trap => some [.trap]
  | .raise =>
    match st.stk with
    | [.ref (.exn a)] => if st.lbls = [] then some (throwing a) else none
    | _ => none
  | _ => none

end Silmaril.Wasm.Cfg.Machine
