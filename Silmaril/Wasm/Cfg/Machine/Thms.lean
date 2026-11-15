module

public import Silmaril.Wasm.Cfg.Machine.Defs
public import Silmaril.Wasm.Cfg.Region.Defs
import Silmaril.Proofs.Wasm.Cfg.Machine

@[expose] public section

/-!
# The block-CFG machine follows the extracted CFG

* `mstep_from_block`: the machine steps only from block nodes; `exit`, `trap` and `raise` are
  sinks.
* **`mstep_edge`**: every step from block `b` (of a state satisfying `MInv`) goes to a
  `Cfg.Edge` successor of `b` (`succOf`), **or** to the `trap` sink because the block's
  straight-line body trapped (`bodyTrap`), **or**, for a caught exception, along a catch edge
  of an enclosing `try_table` block (`CatchEdge`). Body traps are not flow edges of `succOf`:
  in the CFG they are instruction effects (`instrEffects`), not control successors; caught
  exceptions are edges of the `try_table` block, not of the throwing one. The statement keeps
  the three apart.
* The label invariant `codeAt` (Defs): the region code a machine state stands for, with each
  label frame as Core's `LABEL` (and `HANDLER` for `try_table`, by the explicit `tryT` flag).
  `wrap_mono` lifts region-run inclusion through it; `enter_block_sound` proves entering a
  `block` sound.
* The sequence layer of adequacy: `lookup_eq` (a `BlockId` names block `idx` of the sequence
  `seqAt body seq`), `restAt_cons`, `restAt_zero`, and `fall_sound`/`fall_complete` (a
  fall-through step agrees with `Region.Run` on the rest of the sequence).

* Loop re-entry: label frames carry their block type (`LFrame.bt`); a branch to a `loop` label
  checks at run time that it resolves to the label's arity of parameters. Under frame coherence
  (`FramesOk`: each frame describes the structured instruction at its level),
  `br_loop_step_sound`/`brIfTaken_loop_step_sound` prove re-entry sound, and
  `levelLoop_of_framesOk` discharges the CFG side condition of the non-loop branch theorems.

`mstep_edge` is a graph fact, true by construction of `MStep` from `entry`/`labels`/`resolveT`.
* The state invariant `MInv` (coherent frames at blocks) is preserved by every step
  (`mstep_inv`), and with it each step's soundness composes: **`run_sound`** (any run to a sink)
  and **`run_sound_initial`** (from `cfgEntry`) prove machine runs are `Region.Run` runs of the
  function body, ending as the sink says (`Ends`: values by fall-through or `return`, `trap`, or
  the thrown exception).

* Handler catching: a throw caught by the first `try_table` frame whose clauses match branches
  to the clause's label (`MStep.catch_`, `catch_step_sound`); an exception that every handler
  lets pass raises (`raise_pass_sound`). Both are part of `run_sound`.

Not claimed here: completeness (every region run is a machine run) and divergence. Calls,
`br_table` and `br_on_*` terminators have no machine step yet.
-/

namespace Silmaril.Wasm.Cfg.Machine

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H} {body : Expr}

theorem mstep_from_block {st st' : MState H} (h : MStep P host body st st') :
    ∃ b, st.node = .block b :=
  Proofs.Machine.mstep_from_block h

/-- **Every machine step from a state satisfying the invariant follows the extracted block
CFG**: an edge of its block, a trap of the block's body (an instruction effect, not a flow
edge), or a catch edge of an enclosing `try_table` (a caught exception). -/
theorem mstep_edge {st st' : MState H} (h : MStep P host body st st') (hok : MInv body st)
    {b : BlockId} (hn : st.node = .block b) :
    Edge body b st'.node ∨ st'.node = .trap ∨ CatchEdge body b st'.node :=
  Proofs.Machine.mstep_edge h hok hn

theorem lookup_eq (b : BlockId) :
    lookup body b = (seqAt body b.seq).bind fun c => (segment c)[b.idx]? :=
  Proofs.Machine.lookup_eq body b

theorem restAt_cons {c : List Instr} {i : Nat} {sg : Segment} (h : (segment c)[i]? = some sg) :
    restAt c i = sg.instrs ++ restAt c (i + 1) :=
  Proofs.Machine.restAt_cons h

theorem restAt_zero (c : List Instr) : restAt c 0 = c := Proofs.Machine.restAt_zero c

/-- A fall-through step is sound for the region semantics of the rest of the sequence. -/
theorem fall_sound {c : List Instr} {i : Nat} {sg : Segment} (hsg : (segment c)[i]? = some sg)
    (ht : sg.term = none) {s s₁ s' : Store H} {f f₁ f' : Frame} {stk stk₁ : List Val}
    {o : Region.Out}
    (hr : Region.Run P host s f stk (expression sg.body) s₁ f₁ (.normal stk₁))
    (hk : Region.Run P host s₁ f₁ stk₁ (expression (restAt c (i + 1))) s' f' o) :
    Region.Run P host s f stk (expression (restAt c i)) s' f' o :=
  Proofs.Machine.fall_sound hsg ht hr hk

/-- And complete: a region run of the rest from a terminator-free block runs its body first. -/
theorem fall_complete {c : List Instr} {i : Nat} {sg : Segment} (hsg : (segment c)[i]? = some sg)
    (ht : sg.term = none) {s s' : Store H} {f f' : Frame} {stk : List Val} {o : Region.Out}
    (h : Region.Run P host s f stk (expression (restAt c i)) s' f' o) :
    ∃ s₁ f₁ o₁, Region.Run P host s f stk (expression sg.body) s₁ f₁ o₁ ∧
      Region.Then P host s₁ f₁ o₁ (expression (restAt c (i + 1))) s' f' o :=
  Proofs.Machine.fall_complete hsg ht h

/-! ## The label invariant -/

/-- **Context lifting**: region-run inclusion of inner codes lifts through the label frames. -/
theorem wrap_mono {s s₁ : Store H} {f f₁ : Frame} (rp : List SeqStep) (ls : List LFrame)
    {inner inner' X X' : List Admin} (hX : wrap body rp ls inner = some X)
    (hX' : wrap body rp ls inner' = some X')
    (hb : ∀ {o : Region.Out} {s₂ : Store H} {f₂ : Frame},
      Region.Run P host s₁ f₁ [] inner' s₂ f₂ o → Region.Run P host s f [] inner s₂ f₂ o)
    {o : Region.Out} {s₂ : Store H} {f₂ : Frame} :
    Region.Run P host s₁ f₁ [] X' s₂ f₂ o → Region.Run P host s f [] X s₂ f₂ o :=
  Proofs.Machine.wrap_mono rp ls hX hX' hb

/-- **Entering a `block` is sound for the label invariant** (`codeAt`): every region run of the
code after entering a non-empty arm is a region run of the code before. -/
theorem enter_block_sound {b : BlockId} {sg : Segment} {c c' : List Instr} {bt : BlockType}
    {ls : List LFrame} {s s₁ : Store H} {f f₁ : Frame} {stk ws us : List Val}
    {t₁ t₂ : List Validation.CValType} {X X' : List Admin}
    (hc : seqAt body b.seq = some c) (hsg : (segment c)[b.idx]? = some sg)
    (ht : sg.term = some (.block bt c'))
    (hr : Region.Run P host s f stk (expression sg.body) s₁ f₁ (.normal (ws ++ us)))
    (hbt : f₁.module.blockType? bt = some (t₁, t₂)) (hm : us.length = t₁.length)
    (hX : codeAt body b stk ls = some X)
    (hX' : codeAt body ⟨b.seq ++ [(b.idx, 0)], 0⟩ us (⟨t₂.length, ws, false, false, [], bt⟩ :: ls) =
      some X')
    {o : Region.Out} {s₂ : Store H} {f₂ : Frame} :
    Region.Run P host s₁ f₁ [] X' s₂ f₂ o → Region.Run P host s f [] X s₂ f₂ o :=
  Proofs.Machine.enter_block_sound hc hsg ht hr hbt hm hX hX'

/-- **Entering any structured terminator is sound for the label invariant**: `block`, `loop`,
`if` (its condition picks the arm), `try_table` (its frame sits in a `HANDLER`), for a
non-empty arm. -/
theorem enter_sound {b : BlockId} {sg : Segment} {c c' : List Instr} {i : Instr} {a : Nat}
    {bt : BlockType} {loop tryT : Bool} {cs : List Catch} {ls : List LFrame} {s s₁ : Store H}
    {f f₁ : Frame} {stk stk₁ ws us : List Val} {t₁ t₂ : List Validation.CValType}
    {X X' : List Admin}
    (hc : seqAt body b.seq = some c) (hsg : (segment c)[b.idx]? = some sg)
    (ht : sg.term = some i) (harm : armOf i a = some c') (hkind : StructKind i bt loop tryT cs)
    (hr : Region.Run P host s f stk (expression sg.body) s₁ f₁ (.normal stk₁))
    (hcond : CondArm i stk₁ a ws us)
    (hbt : f₁.module.blockType? bt = some (t₁, t₂)) (hm : us.length = t₁.length)
    (hX : codeAt body b stk ls = some X)
    (hX' : codeAt body ⟨b.seq ++ [(b.idx, a)], 0⟩ us
      (⟨labelArity loop t₁ t₂, ws, loop, tryT, cs, bt⟩ :: ls) = some X')
    {o : Region.Out} {s₂ : Store H} {f₂ : Frame} :
    Region.Run P host s₁ f₁ [] X' s₂ f₂ o → Region.Run P host s f [] X s₂ f₂ o :=
  Proofs.Machine.enter_sound hc hsg ht harm hkind hr hcond hbt hm hX hX'

/-- **Leaving finished sequences up to their continuation is sound** (`goto` to `contRev`,
popping label frames with `popL`, against Core's `label-vals`/`handler-vals`). -/
theorem cont_sound {s : Store H} {f : Frame} (rp : List SeqStep) (ls : List LFrame)
    (W : List Val) {X Y : List Admin} (hX : wrap body rp ls (vals W) = some X)
    (hY : codeOf body (goto (contRev body rp) rp.length ls W s f) = some Y)
    {o : Region.Out} {s₂ : Store H} {f₂ : Frame} :
    Region.Run P host s f [] Y s₂ f₂ o → Region.Run P host s f [] X s₂ f₂ o :=
  Proofs.Machine.cont_sound rp ls W hX hY

/-- **A machine fall-through step is sound for the label invariant** (`codeAt`/`codeOf`),
including leaving finished sequences. -/
theorem fall_step_sound {b : BlockId} {sg : Segment} {stk stk₁ : List Val} {ls : List LFrame}
    {s s₁ : Store H} {f f₁ : Frame} {X Y : List Admin}
    (hb : lookup body b = some sg) (ht : sg.term = none)
    (hr : Region.Run P host s f stk (expression sg.body) s₁ f₁ (.normal stk₁))
    (hX : codeAt body b stk ls = some X)
    (hY : codeOf body (goto (entry body b.seq (b.idx + 1)) b.seq.length ls stk₁ s₁ f₁) = some Y)
    {o : Region.Out} {s₂ : Store H} {f₂ : Frame} :
    Region.Run P host s₁ f₁ [] Y s₂ f₂ o → Region.Run P host s f [] X s₂ f₂ o :=
  Proofs.Machine.fall_step_sound hb ht hr hX hY

/-- **A raise step is sound when no enclosing frame is a `try_table` handler**: the code the
machine stood for throws the same exception (its address is the `raise` state's stack), with the
same final store and frame. The general case, where handlers let the exception pass, is
`raise_pass_sound`. -/
theorem raise_sound {b : BlockId} {sg : Segment} {stk stk₁ : List Val} {ls : List LFrame}
    {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {i : Instr} {a : Nat} {X : List Admin}
    (hb : lookup body b = some sg) (ht : sg.term = some i)
    (hr : Region.Run P host s f stk (expression sg.body) s₁ f₁ (.normal stk₁))
    (hth : Region.Run P host s₁ f₁ stk₁ [.plain i] s₂ f₂ (.throw a))
    (hT : ∀ L ∈ ls, L.tryT = false) (hX : codeAt body b stk ls = some X) :
    Region.Run P host s f [] X s₂ f₂ (.throw a) :=
  Proofs.Machine.raise_sound hb ht hr hth hT hX

/-- **A machine `br` step to a non-loop label is sound for the label invariant.** The step
carries its run-time arity check (`harity`); `hloop`/`hlev` say the target label is not a `loop`,
both in the frame and in the extracted CFG (`levelLoop`). Loop re-entry is not covered yet. -/
theorem br_step_sound {b : BlockId} {sg : Segment} {stk stk₁ : List Val} {ls : List LFrame}
    {s s₁ : Store H} {f f₁ : Frame} {l : LabelIdx} {L : LFrame} {X Y : List Admin}
    (hb : lookup body b = some sg) (ht : sg.term = some (.br l))
    (hr : Region.Run P host s f stk (expression sg.body) s₁ f₁ (.normal stk₁))
    (hL : ls[l.toNat]? = some L) (harity : L.arity ≤ (brVals l.toNat ls stk₁).length)
    (hloop : L.loop = false)
    (hlev : levelLoop body b.seq.reverse l.toNat = false)
    (hX : codeAt body b stk ls = some X)
    (hY : codeOf body (goto (resolveT (labels body b.seq) l) (b.seq.length - (l.toNat + 1))
      (ls.drop (l.toNat + 1)) (L.outer ++ topVals L.arity (brVals l.toNat ls stk₁)) s₁ f₁) = some Y)
    {o : Region.Out} {s₂ : Store H} {f₂ : Frame} :
    Region.Run P host s₁ f₁ [] Y s₂ f₂ o → Region.Run P host s f [] X s₂ f₂ o :=
  Proofs.Machine.br_step_sound hb ht hr hL harity hloop hlev hX hY

/-- **A `br_if` not taken is sound** for the label invariant. -/
theorem brIfNot_step_sound {b : BlockId} {sg : Segment} {stk stk₁ : List Val} {ls : List LFrame}
    {s s₁ : Store H} {f f₁ : Frame} {l : LabelIdx} {X Y : List Admin}
    (hb : lookup body b = some sg) (ht : sg.term = some (.brIf l))
    (hr : Region.Run P host s f stk (expression sg.body) s₁ f₁ (.normal (stk₁ ++ [.i32 0])))
    (hX : codeAt body b stk ls = some X)
    (hY : codeOf body (goto (entry body b.seq (b.idx + 1)) b.seq.length ls stk₁ s₁ f₁) = some Y)
    {o : Region.Out} {s₂ : Store H} {f₂ : Frame} :
    Region.Run P host s₁ f₁ [] Y s₂ f₂ o → Region.Run P host s f [] X s₂ f₂ o :=
  Proofs.Machine.brIfNot_step_sound hb ht hr hX hY

/-- **A `br_if` taken to a non-loop label is sound**, with the run-time arity check. -/
theorem brIfTaken_step_sound {b : BlockId} {sg : Segment} {stk stk₁ : List Val}
    {ls : List LFrame} {s s₁ : Store H} {f f₁ : Frame} {l : LabelIdx} {L : LFrame} {k : BitVec 32}
    {X Y : List Admin} (hb : lookup body b = some sg) (ht : sg.term = some (.brIf l))
    (hr : Region.Run P host s f stk (expression sg.body) s₁ f₁ (.normal (stk₁ ++ [.i32 k])))
    (hk : k ≠ 0) (hL : ls[l.toNat]? = some L) (harity : L.arity ≤ (brVals l.toNat ls stk₁).length)
    (hloop : L.loop = false) (hlev : levelLoop body b.seq.reverse l.toNat = false)
    (hX : codeAt body b stk ls = some X)
    (hY : codeOf body (goto (resolveT (labels body b.seq) l) (b.seq.length - (l.toNat + 1))
      (ls.drop (l.toNat + 1)) (L.outer ++ topVals L.arity (brVals l.toNat ls stk₁)) s₁ f₁) = some Y)
    {o : Region.Out} {s₂ : Store H} {f₂ : Frame} :
    Region.Run P host s₁ f₁ [] Y s₂ f₂ o → Region.Run P host s f [] X s₂ f₂ o :=
  Proofs.Machine.brIfTaken_step_sound hb ht hr hk hL harity hloop hlev hX hY

/-- **Entering an empty arm is sound**: the frame is pushed and immediately left. -/
theorem enter_empty_sound {b : BlockId} {sg : Segment} {c : List Instr} {i : Instr} {a : Nat}
    {bt : BlockType} {loop tryT : Bool} {cs : List Catch} {ls : List LFrame} {s s₁ : Store H}
    {f f₁ : Frame} {stk stk₁ ws us : List Val} {t₁ t₂ : List Validation.CValType}
    {X Y : List Admin}
    (hc : seqAt body b.seq = some c) (hsg : (segment c)[b.idx]? = some sg)
    (ht : sg.term = some i) (harm : armOf i a = some []) (hkind : StructKind i bt loop tryT cs)
    (hr : Region.Run P host s f stk (expression sg.body) s₁ f₁ (.normal stk₁))
    (hcond : CondArm i stk₁ a ws us)
    (hbt : f₁.module.blockType? bt = some (t₁, t₂)) (hm : us.length = t₁.length)
    (hX : codeAt body b stk ls = some X)
    (hY : codeOf body (goto (contRev body ((b.idx, a) :: b.seq.reverse)) (b.seq.length + 1)
      (⟨labelArity loop t₁ t₂, ws, loop, tryT, cs, bt⟩ :: ls) us s₁ f₁) = some Y)
    {o : Region.Out} {s₂ : Store H} {f₂ : Frame} :
    Region.Run P host s₁ f₁ [] Y s₂ f₂ o → Region.Run P host s f [] X s₂ f₂ o :=
  Proofs.Machine.enter_empty_sound hc hsg ht harm hkind hr hcond hbt hm hX hY

/-! ## Loop re-entry and frame coherence -/

/-- **Under coherent frames** (`FramesOk`), the CFG's `loop` flag of an enclosing level is the
frame's: this discharges the `levelLoop` side condition of `br_step_sound`. -/
theorem levelLoop_of_framesOk {k : Nat} {rp : List SeqStep} {ls : List LFrame} {L : LFrame}
    (hok : FramesOk body rp ls) (hL : ls[k]? = some L) : levelLoop body rp k = L.loop :=
  Proofs.Machine.levelLoop_of_framesOk k rp ls hok hL

/-- **A machine `br` step to a `loop` label is sound for the label invariant** (loop
re-entry), under coherent frames, with the step's run-time checks: the stack holds the label's
arity, and the frame's block type resolves to that many parameters (`MStep.br`'s `hlbt`). -/
theorem br_loop_step_sound {b : BlockId} {sg : Segment} {stk stk₁ : List Val}
    {ls : List LFrame} {s s₁ : Store H} {f f₁ : Frame} {l : LabelIdx} {L : LFrame}
    {t₁ t₂ : List Validation.CValType} {X Y : List Admin} (hb : lookup body b = some sg)
    (ht : sg.term = some (.br l))
    (hr : Region.Run P host s f stk (expression sg.body) s₁ f₁ (.normal stk₁))
    (hL : ls[l.toNat]? = some L) (harity : L.arity ≤ (brVals l.toNat ls stk₁).length)
    (hloop : L.loop = true)
    (hbt : f₁.module.blockType? L.bt = some (t₁, t₂)) (hlen : t₁.length = L.arity)
    (hok : FramesOk body b.seq.reverse ls) (hX : codeAt body b stk ls = some X)
    (hY : codeOf body (goto (resolveT (labels body b.seq) l) (b.seq.length - l.toNat)
      (L :: ls.drop (l.toNat + 1)) (topVals L.arity (brVals l.toNat ls stk₁)) s₁ f₁) = some Y)
    {o : Region.Out} {s₂ : Store H} {f₂ : Frame} :
    Region.Run P host s₁ f₁ [] Y s₂ f₂ o → Region.Run P host s f [] X s₂ f₂ o :=
  Proofs.Machine.br_loop_step_sound hb ht hr hL harity hloop hbt hlen hok hX hY

/-- **A taken `br_if` to a `loop` label is sound** (loop re-entry), under coherent frames. -/
theorem brIfTaken_loop_step_sound {b : BlockId} {sg : Segment} {stk stk₁ : List Val}
    {ls : List LFrame} {s s₁ : Store H} {f f₁ : Frame} {l : LabelIdx} {L : LFrame}
    {k : BitVec 32} {t₁ t₂ : List Validation.CValType} {X Y : List Admin}
    (hb : lookup body b = some sg) (ht : sg.term = some (.brIf l))
    (hr : Region.Run P host s f stk (expression sg.body) s₁ f₁ (.normal (stk₁ ++ [.i32 k])))
    (hk : k ≠ 0) (hL : ls[l.toNat]? = some L) (harity : L.arity ≤ (brVals l.toNat ls stk₁).length)
    (hloop : L.loop = true) (hbt : f₁.module.blockType? L.bt = some (t₁, t₂))
    (hlen : t₁.length = L.arity) (hok : FramesOk body b.seq.reverse ls)
    (hX : codeAt body b stk ls = some X)
    (hY : codeOf body (goto (resolveT (labels body b.seq) l) (b.seq.length - l.toNat)
      (L :: ls.drop (l.toNat + 1)) (topVals L.arity (brVals l.toNat ls stk₁)) s₁ f₁) = some Y)
    {o : Region.Out} {s₂ : Store H} {f₂ : Frame} :
    Region.Run P host s₁ f₁ [] Y s₂ f₂ o → Region.Run P host s f [] X s₂ f₂ o :=
  Proofs.Machine.brIfTaken_loop_step_sound hb ht hr hk hL harity hloop hbt hlen hok hX hY

/-! ## The state invariant and whole runs -/

/-- **The machine's steps preserve the state invariant** (`MInv`: coherent frames at blocks,
no frames left at `exit` and `raise`). -/
theorem mstep_inv {st st₁ : MState H} (h : MStep P host body st st₁) (hok : MInv body st) :
    MInv body st₁ :=
  have ⟨_, hX⟩ := Proofs.Machine.codeOf_of_ok hok
  (Proofs.Machine.mstep_sound h hok hX).1

/-- A state satisfying the invariant stands for region code. -/
theorem codeOf_of_inv {st : MState H} (hok : MInv body st) : ∃ X, codeOf body st = some X :=
  Proofs.Machine.codeOf_of_ok hok

/-- **An `unreachable` terminator is sound**: the code traps, with the body's final store. -/
theorem trap_sound {b : BlockId} {sg : Segment} {stk stk₁ : List Val} {ls : List LFrame}
    {s s₁ : Store H} {f f₁ : Frame} {X : List Admin}
    (hb : lookup body b = some sg) (ht : sg.term = some .unreachable)
    (hr : Region.Run P host s f stk (expression sg.body) s₁ f₁ (.normal stk₁))
    (hX : codeAt body b stk ls = some X) : Region.Run P host s f [] X s₁ f₁ .trap :=
  Proofs.Machine.trap_sound hb ht hr hX

/-- **A trap in a block's straight-line body is sound.** -/
theorem bodyTrap_sound {b : BlockId} {sg : Segment} {stk : List Val} {ls : List LFrame}
    {s s₁ : Store H} {f f₁ : Frame} {X : List Admin} (hb : lookup body b = some sg)
    (hr : Region.Run P host s f stk (expression sg.body) s₁ f₁ .trap)
    (hX : codeAt body b stk ls = some X) : Region.Run P host s f [] X s₁ f₁ .trap :=
  Proofs.Machine.bodyTrap_sound hb hr hX

/-- **A `return` is sound**: the code returns the block's values, over the label frames' outer
values (Core keeps the top values a function returns). -/
theorem ret_sound {b : BlockId} {sg : Segment} {stk stk₁ : List Val} {ls : List LFrame}
    {s s₁ : Store H} {f f₁ : Frame} {X : List Admin}
    (hb : lookup body b = some sg) (ht : sg.term = some .return_)
    (hr : Region.Run P host s f stk (expression sg.body) s₁ f₁ (.normal stk₁))
    (hX : codeAt body b stk ls = some X) :
    ∃ W, Region.Run P host s f [] X s₁ f₁ (.ret (W ++ stk₁)) :=
  Proofs.Machine.ret_sound hb ht hr hX

/-- **Whole-run soundness**: a machine run from a state satisfying the invariant to a sink
(`exit`, `trap`, `raise`) is a region run of the code that state stands for, from its store and
frame to the sink's, ending as the sink says (`Ends`). -/
theorem run_sound {st st' : MState H} (h : Relation.ReflTransGen (MStep P host body) st st')
    (hs : st'.node.IsSink) (hok : MInv body st) {X : List Admin}
    (hX : codeOf body st = some X) :
    ∃ o, Ends st' o ∧ Region.Run P host st.store st.frame [] X st'.store st'.frame o :=
  Proofs.Machine.run_sound h hs hok hX

/-- **Whole-run soundness from the CFG entry**: a machine run of a function body from its
initial state (`cfgEntry`, empty stack, no label frames) to a sink is a region run of the body
(`Region.Run` of `expression body`, from the initial store and frame to the sink's). -/
theorem run_sound_initial {s : Store H} {f : Frame} {st' : MState H}
    (h : Relation.ReflTransGen (MStep P host body) (initial body s f) st')
    (hs : st'.node.IsSink) :
    ∃ o, Ends st' o ∧ Region.Run P host s f [] (expression body) st'.store st'.frame o :=
  Proofs.Machine.run_sound_initial h hs

/-! ## Handler catching -/

/-- **An uncaught raise step is sound**: when every enclosing handler lets the exception pass
(no clause matches), the code throws it, with the same final store and frame. -/
theorem raise_pass_sound {b : BlockId} {sg : Segment} {stk stk₁ : List Val}
    {ls : List LFrame} {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {i : Instr} {a : Nat}
    {X : List Admin} (hb : lookup body b = some sg) (ht : sg.term = some i)
    (hr : Region.Run P host s f stk (expression sg.body) s₁ f₁ (.normal stk₁))
    (hth : Region.Run P host s₁ f₁ stk₁ [.plain i] s₂ f₂ (.throw a))
    (hT : ∀ (k : Nat) (L : LFrame), ls[k]? = some L → L.tryT = true →
      Region.Catches s₂ f₂ a L.catches none)
    (hX : codeAt body b stk ls = some X) :
    Region.Run P host s f [] X s₂ f₂ (.throw a) :=
  Proofs.Machine.raise_pass_sound hb ht hr hth hT hX

/-- **A caught throw is sound** (`MStep.catch_`): frames below `j` let the exception pass, the
`try_table` frame `j` catches it with its first matching clause (values `us`, label `l`), and
the machine branches to label `j + 1 + l` with the handler's outer values under `us`, as Core's
`handler` does, under coherent frames and the branch's run-time checks. -/
theorem catch_step_sound {b : BlockId} {sg : Segment} {stk stk₁ us : List Val}
    {ls : List LFrame} {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {i : Instr} {a j : Nat}
    {L L' : LFrame} {l : LabelIdx} {X Y : List Admin}
    (hb : lookup body b = some sg) (ht : sg.term = some i)
    (hr : Region.Run P host s f stk (expression sg.body) s₁ f₁ (.normal stk₁))
    (hth : Region.Run P host s₁ f₁ stk₁ [.plain i] s₂ f₂ (.throw a))
    (hpass : ∀ (k : Nat) (L : LFrame), k < j → ls[k]? = some L → L.tryT = true →
      Region.Catches s₂ f₂ a L.catches none)
    (hL : ls[j]? = some L) (hT : L.tryT = true)
    (hc : Region.Catches s₂ f₂ a L.catches (some (us, l)))
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
        some Y)
    {o : Region.Out} {s₃ : Store H} {f₃ : Frame} :
    Region.Run P host s₂ f₂ [] Y s₃ f₃ o → Region.Run P host s f [] X s₃ f₃ o :=
  Proofs.Machine.catch_step_sound hb ht hr hth hpass hL hT hc hL' harity hlbt hok hX hY

end Silmaril.Wasm.Cfg.Machine
