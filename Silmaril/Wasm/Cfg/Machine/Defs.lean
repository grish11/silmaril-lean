module

public import Silmaril.Wasm.Cfg.BlockCfg.Defs
public import Silmaril.Wasm.Cfg.Region.Defs
public import Silmaril.Foundations.InfiniteTrace

@[expose] public section

/-!
# An executable machine over the extracted basic-block CFG

`MStep P host body` steps a machine whose control state is a node of the extracted block CFG
(`Cfg.Target`, blocks named by `BlockId` and found by `lookup`). Each step runs one basic block
(`Segment`): its simple body by the region semantics (`Region.Run`, call-free, straight-line),
then its terminator. The terminator moves to a node computed by the same functions the CFG
uses (`entry`, `labels`, `resolveT`), so that every machine step follows a `Cfg.Edge`
(`Machine/Thms.lean`). That is a graph fact only. Agreement with `Region.Run` is proved step by
step for the label invariant (`codeAt`, below) in `Machine/Thms.lean`; whole-run adequacy is a
separate obligation.

The data state is the value stack, the store, the frame and a stack of label frames
(`LFrame`), one per enclosing structured instruction: its branch arity, the values held
outside it, whether it is a `loop`, its `catch` clauses and its block type (a branch to a
`loop` re-enters it, looking the block type up again as Core's `loop` rule does). Leaving
sequences pops label frames as Core's `label-vals` does (`popL`). A branch carries the stack
under the outer values of the frames it leaves (`brVals`), as Core's labels collect them.
Exceptions, returns and traps go to the sink nodes `raise`, `exit` and `trap`; an exception that a `try_table` frame catches (its first matching
`catch` clause) branches to the clause's label instead. `br_table` and `br_on_*` read their
operands as Core does (`BrStep`) and then branch or fall through.

**Calls.** `MStepC P host C body` is the same machine with the `call`s of block bodies answered
by an oracle `C : Abstract.CallRel H`, as `Region.RunC P host C` answers them: the callee is not
entered, and its answer is pushed (or traps, or throws). An exception thrown by a call in a
block's body is raised (`bodyRaise`) or caught by a `try_table` frame (`bodyCatch`), as one
thrown by a `throw` terminator is. `MStep P host body := MStepC P host noCall body` is the
call-free machine. A tail call of null traps (`tailNull`). A tail call of a function (`tail`)
is answered by `C` at the function's frame, which Core replaces by the callee's: the machine
moves to the sink of the answer (`tailEnd`).
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
  /-- The block type of the structured instruction. A branch to a `loop` label re-enters the
  `loop`, which looks this block type up again (Core's `loop` rule). -/
  bt : BlockType
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

/-- The top `n` values of a stack (all of it if shorter). -/
abbrev topVals (n : Nat) (V : List Val) : List Val := V.drop (V.length - n)

/-- **The values a branch to the `k`-th label carries**: the stack, under the outer values of the
`k` frames it leaves (innermost nearest), as Core's `label` collects them (`labelBrSucc`). The
target label keeps the top values of these. -/
def brVals : Nat → List LFrame → List Val → List Val
  | 0, _, stk => stk
  | _ + 1, [], stk => stk
  | k + 1, L :: ls, stk => brVals k ls (L.outer ++ stk)

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

/-- `return_call`, `return_call_ref` and `return_call_indirect`. -/
def _root_.Silmaril.Wasm.Instr.IsTailCall : Instr → Prop
  | .returnCall _ | .returnCallRef _ | .returnCallIndirect .. => True
  | _ => False

/-- **The state a function ends in after a tail call**, from the callee's flow `fl` (its final
store `s`, the caller's frame `f`): its top `rs` results at `exit`, `trap`, or its exception at
`raise`. The function's label frames are gone: Core replaced its frame by the callee's. -/
def tailEnd (rs : Nat) (s : Store H) (f : Frame) : Binaryen.Flow → Option (MState H)
  | .trap => some ⟨.trap, [], [], s, f⟩
  | .throw t => some ⟨.raise, [.ref (.exn t)], [], s, f⟩
  | fl => fl.retVals.map fun vs => ⟨.exit, (vs.take rs).reverse, [], s, f⟩

/-- **One block step**, with calls answered by the oracle `C`. From block `b`, run its simple
body (`Region.RunC P host C`, to values; a `call` in it is answered by `C` as `RunC.call` does),
then its terminator. -/
inductive MStepC (P : Profile) (host : HostSemantics H) (C : Abstract.CallRel H) (body : Expr) :
    MState H → MState H → Prop where
  /-- No terminator: fall through to the next position of the sequence. -/
  | fall {b : BlockId} {sg : Segment} {stk stk₁ : List Val} {ls : List LFrame} {s s₁ : Store H}
      {f f₁ : Frame} (hb : lookup body b = some sg) (ht : sg.term = none)
      (hr : RunC P host C s f stk (expression sg.body) s₁ f₁ (.normal stk₁)) :
      MStepC P host C body ⟨.block b, stk, ls, s, f⟩
        (goto (entry body b.seq (b.idx + 1)) b.seq.length ls stk₁ s₁ f₁)
  /-- `br l`: keep the label's top values; re-enter a loop, or leave the label's sequence. The
  values carried are the stack under the left frames' outer values (`brVals`), as in Core; the
  step checks at run time that they hold the label's arity (`harity`); with fewer the machine
  does not step (Core has no branch rule there either). Re-entering a `loop` also
  checks that the frame's block type resolves in the current module with as many parameters as
  the label's arity (`hlbt`), which Core's `loop` rule needs. -/
  | br {b : BlockId} {sg : Segment} {stk stk₁ : List Val} {ls : List LFrame} {s s₁ : Store H}
      {f f₁ : Frame} {l : LabelIdx} {L : LFrame} (hb : lookup body b = some sg)
      (ht : sg.term = some (.br l))
      (hr : RunC P host C s f stk (expression sg.body) s₁ f₁ (.normal stk₁))
      (hL : ls[l.toNat]? = some L) (harity : L.arity ≤ (brVals l.toNat ls stk₁).length)
      (hlbt : L.loop = true → ∃ t₁ t₂, f₁.module.blockType? L.bt = some (t₁, t₂) ∧
        t₁.length = L.arity) :
      MStepC P host C body ⟨.block b, stk, ls, s, f⟩
        (if L.loop then
          goto (resolveT (labels body b.seq) l) (b.seq.length - l.toNat)
            (L :: ls.drop (l.toNat + 1)) (topVals L.arity (brVals l.toNat ls stk₁)) s₁ f₁
        else
          goto (resolveT (labels body b.seq) l) (b.seq.length - (l.toNat + 1))
            (ls.drop (l.toNat + 1)) (L.outer ++ topVals L.arity (brVals l.toNat ls stk₁)) s₁ f₁)
  /-- `br_if l` with a nonzero condition branches like `br l`. -/
  | brIfTaken {b : BlockId} {sg : Segment} {stk stk₁ : List Val} {ls : List LFrame}
      {s s₁ : Store H} {f f₁ : Frame} {l : LabelIdx} {L : LFrame} {k : BitVec 32}
      (hb : lookup body b = some sg) (ht : sg.term = some (.brIf l))
      (hr : RunC P host C s f stk (expression sg.body) s₁ f₁ (.normal (stk₁ ++ [.i32 k])))
      (hk : k ≠ 0) (hL : ls[l.toNat]? = some L) (harity : L.arity ≤ (brVals l.toNat ls stk₁).length)
      (hlbt : L.loop = true → ∃ t₁ t₂, f₁.module.blockType? L.bt = some (t₁, t₂) ∧
        t₁.length = L.arity) :
      MStepC P host C body ⟨.block b, stk, ls, s, f⟩
        (if L.loop then
          goto (resolveT (labels body b.seq) l) (b.seq.length - l.toNat)
            (L :: ls.drop (l.toNat + 1)) (topVals L.arity (brVals l.toNat ls stk₁)) s₁ f₁
        else
          goto (resolveT (labels body b.seq) l) (b.seq.length - (l.toNat + 1))
            (ls.drop (l.toNat + 1)) (L.outer ++ topVals L.arity (brVals l.toNat ls stk₁)) s₁ f₁)
  /-- `br_if l` with a zero condition falls through. -/
  | brIfNot {b : BlockId} {sg : Segment} {stk stk₁ : List Val} {ls : List LFrame}
      {s s₁ : Store H} {f f₁ : Frame} {l : LabelIdx} (hb : lookup body b = some sg)
      (ht : sg.term = some (.brIf l))
      (hr : RunC P host C s f stk (expression sg.body) s₁ f₁ (.normal (stk₁ ++ [.i32 0]))) :
      MStepC P host C body ⟨.block b, stk, ls, s, f⟩
        (goto (entry body b.seq (b.idx + 1)) b.seq.length ls stk₁ s₁ f₁)
  /-- A data-dependent branch terminator (`br_table`, `br_on_*`) that branches: it reads its
  operands (`BrStep`) and then branches like `br l`. -/
  | brDataTaken {b : BlockId} {sg : Segment} {stk ws us us' : List Val} {ls : List LFrame}
      {s s₁ : Store H} {f f₁ : Frame} {i : Instr} {l : LabelIdx} {L : LFrame}
      (hb : lookup body b = some sg) (ht : sg.term = some i)
      (hr : RunC P host C s f stk (expression sg.body) s₁ f₁ (.normal (ws ++ us)))
      (hbs : BrStep s₁ f₁ us i us' [.plain (.br l)])
      (hL : ls[l.toNat]? = some L) (harity : L.arity ≤ (brVals l.toNat ls (ws ++ us')).length)
      (hlbt : L.loop = true → ∃ t₁ t₂, f₁.module.blockType? L.bt = some (t₁, t₂) ∧
        t₁.length = L.arity) :
      MStepC P host C body ⟨.block b, stk, ls, s, f⟩
        (if L.loop then
          goto (resolveT (labels body b.seq) l) (b.seq.length - l.toNat)
            (L :: ls.drop (l.toNat + 1)) (topVals L.arity (brVals l.toNat ls (ws ++ us'))) s₁ f₁
        else
          goto (resolveT (labels body b.seq) l) (b.seq.length - (l.toNat + 1))
            (ls.drop (l.toNat + 1))
            (L.outer ++ topVals L.arity (brVals l.toNat ls (ws ++ us'))) s₁ f₁)
  /-- A data-dependent branch terminator (`br_on_*`) that does not branch: fall through with the
  values it leaves. -/
  | brDataNot {b : BlockId} {sg : Segment} {stk ws us us' : List Val} {ls : List LFrame}
      {s s₁ : Store H} {f f₁ : Frame} {i : Instr} (hb : lookup body b = some sg)
      (ht : sg.term = some i)
      (hr : RunC P host C s f stk (expression sg.body) s₁ f₁ (.normal (ws ++ us)))
      (hbs : BrStep s₁ f₁ us i us' []) :
      MStepC P host C body ⟨.block b, stk, ls, s, f⟩
        (goto (entry body b.seq (b.idx + 1)) b.seq.length ls (ws ++ us') s₁ f₁)
  /-- Entering arm `a` of a structured terminator (`block`, `loop`, `if` with its condition,
  `try_table`): push its label frame on the parameters. -/
  | enter {b : BlockId} {sg : Segment} {stk stk₁ ws us : List Val} {ls : List LFrame}
      {s s₁ : Store H} {f f₁ : Frame} {i : Instr} {a : Nat} {c : List Instr} {bt : BlockType}
      {t₁ t₂ : List CValType} {loop tryT : Bool} {cs : List Catch}
      (hb : lookup body b = some sg) (ht : sg.term = some i) (harm : armOf i a = some c)
      (hkind : StructKind i bt loop tryT cs)
      (hr : RunC P host C s f stk (expression sg.body) s₁ f₁ (.normal stk₁))
      (hcond : CondArm i stk₁ a ws us)
      (hbt : f₁.module.blockType? bt = some (t₁, t₂)) (hm : us.length = t₁.length) :
      MStepC P host C body ⟨.block b, stk, ls, s, f⟩
        (goto (entry body (b.seq ++ [(b.idx, a)]) 0) (b.seq.length + 1)
          (⟨labelArity loop t₁ t₂, ws, loop, tryT, cs, bt⟩ :: ls) us s₁ f₁)
  /-- `return` leaves the function. -/
  | ret {b : BlockId} {sg : Segment} {stk stk₁ : List Val} {ls : List LFrame} {s s₁ : Store H}
      {f f₁ : Frame} (hb : lookup body b = some sg) (ht : sg.term = some .return_)
      (hr : RunC P host C s f stk (expression sg.body) s₁ f₁ (.normal stk₁)) :
      MStepC P host C body ⟨.block b, stk, ls, s, f⟩ ⟨.exit, stk₁, [], s₁, f₁⟩
  /-- `br l` to the function label (`l` is the number of label frames, the function boundary):
  leave the function with the block's values, as `return` does. Deeper labels stay invalid. -/
  | brOut {b : BlockId} {sg : Segment} {stk stk₁ : List Val} {ls : List LFrame} {s s₁ : Store H}
      {f f₁ : Frame} {l : LabelIdx} (hb : lookup body b = some sg)
      (ht : sg.term = some (.br l))
      (hr : RunC P host C s f stk (expression sg.body) s₁ f₁ (.normal stk₁))
      (hL : l.toNat = ls.length) :
      MStepC P host C body ⟨.block b, stk, ls, s, f⟩ ⟨.exit, stk₁, [], s₁, f₁⟩
  /-- `br_if l` with a nonzero condition, to the function label. -/
  | brIfOut {b : BlockId} {sg : Segment} {stk stk₁ : List Val} {ls : List LFrame}
      {s s₁ : Store H} {f f₁ : Frame} {l : LabelIdx} {k : BitVec 32}
      (hb : lookup body b = some sg) (ht : sg.term = some (.brIf l))
      (hr : RunC P host C s f stk (expression sg.body) s₁ f₁ (.normal (stk₁ ++ [.i32 k])))
      (hk : k ≠ 0) (hL : l.toNat = ls.length) :
      MStepC P host C body ⟨.block b, stk, ls, s, f⟩ ⟨.exit, stk₁, [], s₁, f₁⟩
  /-- A data-dependent branch (`br_table`, `br_on_*`) that branches to the function label. -/
  | brDataOut {b : BlockId} {sg : Segment} {stk ws us us' : List Val} {ls : List LFrame}
      {s s₁ : Store H} {f f₁ : Frame} {i : Instr} {l : LabelIdx}
      (hb : lookup body b = some sg) (ht : sg.term = some i)
      (hr : RunC P host C s f stk (expression sg.body) s₁ f₁ (.normal (ws ++ us)))
      (hbs : BrStep s₁ f₁ us i us' [.plain (.br l)]) (hL : l.toNat = ls.length) :
      MStepC P host C body ⟨.block b, stk, ls, s, f⟩ ⟨.exit, ws ++ us', [], s₁, f₁⟩
  /-- `unreachable`, or a trap in the block's body. -/
  | trap {b : BlockId} {sg : Segment} {stk : List Val} {ls : List LFrame} {s s₁ : Store H}
      {f f₁ : Frame} (hb : lookup body b = some sg) (ht : sg.term = some .unreachable)
      (hr : ∃ stk₁, RunC P host C s f stk (expression sg.body) s₁ f₁ (.normal stk₁)) :
      MStepC P host C body ⟨.block b, stk, ls, s, f⟩ ⟨.trap, [], [], s₁, f₁⟩
  /-- A terminator that traps when it runs (`throw_ref` on a null reference, or `unreachable`). -/
  | termTrap {b : BlockId} {sg : Segment} {stk stk₁ : List Val} {ls : List LFrame}
      {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {i : Instr} (hb : lookup body b = some sg)
      (ht : sg.term = some i)
      (hr : RunC P host C s f stk (expression sg.body) s₁ f₁ (.normal stk₁))
      (hth : RunC P host C s₁ f₁ stk₁ [.plain i] s₂ f₂ .trap) :
      MStepC P host C body ⟨.block b, stk, ls, s, f⟩ ⟨.trap, [], [], s₂, f₂⟩
  /-- A trap in the block's straight-line body (an effect of one of its instructions). -/
  | bodyTrap {b : BlockId} {sg : Segment} {stk : List Val} {ls : List LFrame} {s s₁ : Store H}
      {f f₁ : Frame} (hb : lookup body b = some sg)
      (hr : RunC P host C s f stk (expression sg.body) s₁ f₁ .trap) :
      MStepC P host C body ⟨.block b, stk, ls, s, f⟩ ⟨.trap, [], [], s₁, f₁⟩
  /-- `throw` and `throw_ref`, uncaught: the terminator runs (allocating the exception for
  `throw`), every enclosing `try_table` frame lets the exception pass (no clause matches,
  `hT`), and the machine moves to the `raise` sink with the exception's address as its stack
  (`[ref (exn a)]`) and the store after the throw. -/
  | raise {b : BlockId} {sg : Segment} {stk stk₁ : List Val} {ls : List LFrame}
      {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {i : Instr} {a : Nat} (hb : lookup body b = some sg)
      (ht : sg.term = some i) (hi : i.IsThrow)
      (hr : RunC P host C s f stk (expression sg.body) s₁ f₁ (.normal stk₁))
      (hth : RunC P host C s₁ f₁ stk₁ [.plain i] s₂ f₂ (.throw a))
      (hT : ∀ (k : Nat) (L : LFrame), ls[k]? = some L → L.tryT = true →
        Catches s₂ f₂ a L.catches none) :
      MStepC P host C body ⟨.block b, stk, ls, s, f⟩ ⟨.raise, [.ref (.exn a)], [], s₂, f₂⟩
  /-- `throw` and `throw_ref`, caught: the frames below `j` let the exception pass (`hpass`),
  and the `try_table` frame `j` catches it with the first matching clause (`Catches`: values
  `us`, label `l`). As Core's `handler` does, this branches to `l` from outside the
  `try_table`, which is label `j + 1 + l` here, with the handler's outer values under `us`.
  The branch is taken as `br` takes it, with the same run-time checks. -/
  | catch_ {b : BlockId} {sg : Segment} {stk stk₁ us : List Val} {ls : List LFrame}
      {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {i : Instr} {a j : Nat} {L L' : LFrame}
      {l : LabelIdx} (hb : lookup body b = some sg) (ht : sg.term = some i) (hi : i.IsThrow)
      (hr : RunC P host C s f stk (expression sg.body) s₁ f₁ (.normal stk₁))
      (hth : RunC P host C s₁ f₁ stk₁ [.plain i] s₂ f₂ (.throw a))
      (hpass : ∀ (k : Nat) (L : LFrame), k < j → ls[k]? = some L → L.tryT = true →
        Catches s₂ f₂ a L.catches none)
      (hL : ls[j]? = some L) (hT : L.tryT = true) (hc : Catches s₂ f₂ a L.catches (some (us, l)))
      (hL' : ls[j + 1 + l.toNat]? = some L')
      (harity : L'.arity ≤ (brVals l.toNat (ls.drop (j + 1)) (L.outer ++ us)).length)
      (hlbt : L'.loop = true → ∃ t₁ t₂, f₂.module.blockType? L'.bt = some (t₁, t₂) ∧
        t₁.length = L'.arity) :
      MStepC P host C body ⟨.block b, stk, ls, s, f⟩
        (if L'.loop then
          goto ((labels body b.seq).getD (j + 1 + l.toNat) .invalid)
            (b.seq.length - (j + 1 + l.toNat)) (L' :: ls.drop (j + 1 + l.toNat + 1))
            (topVals L'.arity (brVals l.toNat (ls.drop (j + 1)) (L.outer ++ us))) s₂ f₂
        else
          goto ((labels body b.seq).getD (j + 1 + l.toNat) .invalid)
            (b.seq.length - (j + 1 + l.toNat + 1)) (ls.drop (j + 1 + l.toNat + 1))
            (L'.outer ++ topVals L'.arity (brVals l.toNat (ls.drop (j + 1)) (L.outer ++ us))) s₂ f₂)
  /-- An exception thrown in the block's straight-line body (by a `call` the oracle answers
  with `throw`), uncaught: every enclosing `try_table` frame lets it pass (`hT`), and the machine
  moves to the `raise` sink as for an uncaught `throw` terminator. -/
  | bodyRaise {b : BlockId} {sg : Segment} {stk : List Val} {ls : List LFrame}
      {s s₁ : Store H} {f f₁ : Frame} {a : Nat} (hb : lookup body b = some sg)
      (hr : RunC P host C s f stk (expression sg.body) s₁ f₁ (.throw a))
      (hT : ∀ (k : Nat) (L : LFrame), ls[k]? = some L → L.tryT = true →
        Catches s₁ f₁ a L.catches none) :
      MStepC P host C body ⟨.block b, stk, ls, s, f⟩ ⟨.raise, [.ref (.exn a)], [], s₁, f₁⟩
  /-- An exception thrown in the block's straight-line body, caught by the `try_table` frame `j`
  as for a caught `throw` terminator (`catch_`), with the same run-time checks. -/
  | bodyCatch {b : BlockId} {sg : Segment} {stk us : List Val} {ls : List LFrame}
      {s s₁ : Store H} {f f₁ : Frame} {a j : Nat} {L L' : LFrame} {l : LabelIdx}
      (hb : lookup body b = some sg)
      (hr : RunC P host C s f stk (expression sg.body) s₁ f₁ (.throw a))
      (hpass : ∀ (k : Nat) (L : LFrame), k < j → ls[k]? = some L → L.tryT = true →
        Catches s₁ f₁ a L.catches none)
      (hL : ls[j]? = some L) (hT : L.tryT = true) (hc : Catches s₁ f₁ a L.catches (some (us, l)))
      (hL' : ls[j + 1 + l.toNat]? = some L')
      (harity : L'.arity ≤ (brVals l.toNat (ls.drop (j + 1)) (L.outer ++ us)).length)
      (hlbt : L'.loop = true → ∃ t₁ t₂, f₁.module.blockType? L'.bt = some (t₁, t₂) ∧
        t₁.length = L'.arity) :
      MStepC P host C body ⟨.block b, stk, ls, s, f⟩
        (if L'.loop then
          goto ((labels body b.seq).getD (j + 1 + l.toNat) .invalid)
            (b.seq.length - (j + 1 + l.toNat)) (L' :: ls.drop (j + 1 + l.toNat + 1))
            (topVals L'.arity (brVals l.toNat (ls.drop (j + 1)) (L.outer ++ us))) s₁ f₁
        else
          goto ((labels body b.seq).getD (j + 1 + l.toNat) .invalid)
            (b.seq.length - (j + 1 + l.toNat + 1)) (ls.drop (j + 1 + l.toNat + 1))
            (L'.outer ++ topVals L'.arity (brVals l.toNat (ls.drop (j + 1)) (L.outer ++ us))) s₁ f₁)

  /-- A tail call of a null reference (`return_call_ref` or `return_call_indirect` on null):
  the terminator ends in a pending tail call of null (`Region.Out.tailNull`), which traps when
  it leaves the function's frame (`return_call_ref-frame-null`). The machine moves to `trap`,
  with the store and frame after the terminator. -/
  | tailNull {b : BlockId} {sg : Segment} {stk stk₁ : List Val} {ls : List LFrame}
      {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {i : Instr} {W : List Val} {c : Admin}
      (hb : lookup body b = some sg) (ht : sg.term = some i) (hi : i.IsTailCall)
      (hr : RunC P host C s f stk (expression sg.body) s₁ f₁ (.normal stk₁))
      (hth : RunC P host C s₁ f₁ stk₁ [.plain i] s₂ f₂ (.tailNull W c)) :
      MStepC P host C body ⟨.block b, stk, ls, s, f⟩ ⟨.trap, [], [], s₂, f₂⟩

  /-- **A tail call of a function, answered at the function's frame.** The terminator
  (`return_call*`) ends in a pending tail call of the function at `a` (`Region.Out.tail`, over
  the values `W`). As Core's `return_call_ref-frame-addr` does, the call is made on the top
  `ps.length` values of the whole stack (under `W`, the label frames' outer values, as
  `brVals` collects them), replacing the function's frame: the oracle `C` answers it, and the
  machine moves to the sink of the answer (`tailEnd`), with no label frame left. The callee's
  exception is not caught by the function's handlers. -/
  | tail {b : BlockId} {sg : Segment} {stk stk₁ : List Val} {ls : List LFrame}
      {s s₁ s₂ s₃ : Store H} {f f₁ f₂ : Frame} {i : Instr} {W W₀ args : List Val} {a : Nat}
      {c : Admin} {fi : FuncInst H} {ps rs : List CValType} {fl : Binaryen.Flow} {st' : MState H}
      (hb : lookup body b = some sg) (ht : sg.term = some i) (hi : i.IsTailCall)
      (hr : RunC P host C s f stk (expression sg.body) s₁ f₁ (.normal stk₁))
      (hth : RunC P host C s₁ f₁ stk₁ [.plain i] s₂ f₂ (.tail W a c))
      (hfi : s₂.funcs[a]? = some fi) (hty : DefType.funcType? fi.type = some (ps, rs))
      (hargs : brVals ls.length ls W = W₀ ++ args) (hn : args.length = ps.length)
      (hcall : C s₂ a args (s₃, fl)) (hend : tailEnd rs.length s₃ f₂ fl = some st') :
      MStepC P host C body ⟨.block b, stk, ls, s, f⟩ st'

/-- **The call-free machine**: `MStepC` with no call answered. -/
abbrev MStep (P : Profile) (host : HostSemantics H) (body : Expr) := MStepC P host noCall body

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

namespace Silmaril.Wasm.Cfg.Machine

/-- Whether the `k`-th enclosing structured instruction (at reversed path `rp`) is a `loop` in the
extracted CFG. -/
def levelLoop (body : Expr) (rp : List SeqStep) (k : Nat) : Bool :=
  match rp.drop k with
  | (m, _) :: rp' => isLoopAt body rp'.reverse m
  | [] => false

end Silmaril.Wasm.Cfg.Machine

namespace Silmaril.Wasm.Cfg.Machine

/-- **Frame coherence**: each label frame describes the structured terminator at its level of
the (reversed) path: its block type, `loop` and `try_table` flags and `catch` clauses are those
of that instruction (`StructKind`), and the path's arm exists. The machine's steps preserve it
(`Machine/Thms.lean`). -/
def FramesOk (body : Expr) : List SeqStep → List LFrame → Prop
  | [], [] => True
  | (m, a) :: rp, L :: ls =>
    (∃ pc sg t c, seqAt body rp.reverse = some pc ∧ (segment pc)[m]? = some sg ∧
      sg.term = some t ∧ armOf t a = some c ∧ StructKind t L.bt L.loop L.tryT L.catches) ∧
    FramesOk body rp ls
  | _, _ => False

end Silmaril.Wasm.Cfg.Machine

namespace Silmaril.Wasm.Cfg.Machine

open Silmaril.Wasm.Execution.Core

/-- **The machine state invariant**: coherent frames at a block (`FramesOk` along its path);
no label frame left at `exit` and `raise`, and the exception's address as `raise`'s stack. The
`invalid` node (a branch to a missing label) is excluded. -/
def MInv (body : Expr) {H : Type} (st : MState H) : Prop :=
  match st.node with
  | .block b => FramesOk body b.seq.reverse st.lbls
  | .exit => st.lbls = []
  | .trap => True
  | .raise => st.lbls = [] ∧ ∃ a, st.stk = [.ref (.exn a)]
  | .invalid => False

/-- The sink nodes: `exit`, `trap` and `raise`. -/
def _root_.Silmaril.Wasm.Cfg.Target.IsSink : Target → Prop
  | .exit | .trap | .raise => True
  | _ => False

/-- **What a run ending in a sink state means**, as a region outcome: at `exit`, the final
values, reached by falling off the end (`normal`), by `return` (`ret`, the values under the
returned ones are the label frames' outer values Core keeps), or by a branch to the function
label (`br 0` out of the body, with the same outer values under the branch's); at `trap`, a trap or a pending
tail call of null (which traps at the function's frame); at `raise`, the thrown exception whose
address is the stack. -/
def Ends {H : Type} (st : MState H) (o : Region.Out) : Prop :=
  match st.node with
  | .exit => o = .normal st.stk ∨ (∃ W, o = .ret (W ++ st.stk)) ∨ ∃ W, o = .br 0 (W ++ st.stk)
  | .trap => o = .trap ∨ ∃ W c, o = .tailNull W c
  | .raise => ∃ a, st.stk = [.ref (.exn a)] ∧ o = .throw a
  | _ => False

/-- **What a run ending in a sink state means, with tail calls answered by `C`**: a region
outcome `o` reached in store `s₂` and frame `f₂`. A pending tail call (`Out.tail W a c`) is
completed at the function's frame: `C` answers the call of `a` on the top `ps.length` values of
`W` from `s₂`, and the state is the sink of that answer (`tailEnd`). Any other outcome ends as
`Ends` says, in the state's own store and frame. -/
def EndsC {H : Type} (C : Abstract.CallRel H) (st : MState H) (s₂ : Store H) (f₂ : Frame) :
    Region.Out → Prop
  | .tail W a _ => ∃ (fi : FuncInst H) (ps rs : List Validation.CValType) (W₀ args : List Val)
      (fl : Binaryen.Flow) (s₃ : Store H), s₂.funcs[a]? = some fi ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧ W = W₀ ++ args ∧
      args.length = ps.length ∧ C s₂ a args (s₃, fl) ∧ tailEnd rs.length s₃ f₂ fl = some st
  | o => Ends st o ∧ st.store = s₂ ∧ st.frame = f₂

/-- The machine's initial state for a function body: the CFG entry (`cfgEntry`), empty stack,
no label frames. -/
def initial {H : Type} (body : Expr) (s : Store H) (f : Frame) : MState H :=
  ⟨cfgEntry body, [], [], s, f⟩

end Silmaril.Wasm.Cfg.Machine

namespace Silmaril.Wasm.Cfg.Machine

/-- **A catch edge of `b`**: an edge of an enclosing `try_table` block `tb` (one whose arm holds
`b`'s sequence) to the label of one of its `catch` clauses. A caught exception thrown in `b`
goes there; the extracted CFG keeps it on the `try_table` block (`succOf`) and marks the
throwing block `unresolvedHandler`. -/
def CatchEdge (body : Expr) (b : BlockId) (t : Target) : Prop :=
  ∃ (tb : BlockId) (a : Nat) (rest : List SeqStep) (sg : Segment) (bt : BlockType)
    (cs : List Catch) (c : List Instr) (cl : Catch),
    b.seq = tb.seq ++ (tb.idx, a) :: rest ∧ lookup body tb = some sg ∧
    sg.term = some (.tryTable bt cs c) ∧ cl ∈ cs ∧ t = resolveT (labels body tb.seq) (catchLabel cl)

end Silmaril.Wasm.Cfg.Machine

namespace Silmaril.Wasm.Cfg.Machine

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
open Silmaril.Wasm.Cfg.Region

/-! ## Divergence with calls -/

/-- **A block whose body reaches a diverging call**: the state is at block `b`, whose
straight-line body is `pre ++ call x :: post`; the prefix `pre` runs (`RunC`, its own calls
answered by `C`) to values `ws ++ us`, and `call x` resolves to the function at `a` (of type
`ps → rs`) on its arguments `us`, a call that `D` says diverges. The oracle `C` answers only
terminating calls; this is the machine's divergence inside a single callee. -/
def BodyCallDiv {H : Type} (P : Profile) (host : HostSemantics H) (C : Abstract.CallRel H)
    (D : Store H → Nat → List Val → Prop) (body : Expr) (st : MState H) : Prop :=
  ∃ (b : BlockId) (sg : Segment) (pre post : List Instr) (x : FuncIdx) (s₁ : Store H)
    (f₁ : Frame) (ws us : List Val) (a : Nat) (fi : FuncInst H) (ps rs : List CValType),
    st.node = .block b ∧ lookup body b = some sg ∧ sg.body = pre ++ .call x :: post ∧
    RunC P host C st.store st.frame st.stk (expression pre) s₁ f₁ (.normal (ws ++ us)) ∧
    s₁.func? f₁ x = some (a, fi) ∧ DefType.funcType? fi.type = some (ps, rs) ∧
    us.length = ps.length ∧ D s₁ a us

/-- **Divergence of the machine with calls**: an infinite run of `MStepC`, or a finite run to a
block whose body reaches a call that `D` says diverges (`BodyCallDiv`). An infinite `MStepC`
run alone is not Core divergence's counterpart: its oracle answers only terminating calls, so it
misses divergence inside a single callee. -/
def MDivC {H : Type} (P : Profile) (host : HostSemantics H) (C : Abstract.CallRel H)
    (D : Store H → Nat → List Val → Prop) (body : Expr) (st : MState H) : Prop :=
  InfiniteTrace (MStepC P host C body) st ∨
    ∃ st', Relation.ReflTransGen (MStepC P host C body) st st' ∧ BodyCallDiv P host C D body st'

end Silmaril.Wasm.Cfg.Machine
