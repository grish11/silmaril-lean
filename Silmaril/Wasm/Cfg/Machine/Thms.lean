module

public import Silmaril.Wasm.Cfg.Machine.Defs
public import Silmaril.Wasm.Cfg.Region.Defs
import Silmaril.Proofs.Wasm.Cfg.Machine

@[expose] public section

/-!
# The block-CFG machine follows the extracted CFG

* `mstep_from_block`: the machine steps only from block nodes; `exit`, `trap` and `raise` are
  sinks.
* **`mstep_edge`**: every step from block `b` goes to a `Cfg.Edge` successor of `b`
  (`succOf`), **or** to the `trap` sink because the block's straight-line body trapped
  (`bodyTrap`). Body traps are not flow edges of `succOf`: in the CFG they are instruction
  effects (`instrEffects`, the conservative trap effect edges), not control successors. The
  statement keeps the two apart.
* The label invariant `codeAt` (Defs): the region code a machine state stands for, with each
  label frame as Core's `LABEL` (and `HANDLER` for `try_table`, by the explicit `tryT` flag).
  `wrap_mono` lifts region-run inclusion through it; `enter_block_sound` proves entering a
  `block` sound.
* The sequence layer of adequacy: `lookup_eq` (a `BlockId` names block `idx` of the sequence
  `seqAt body seq`), `restAt_cons`, `restAt_zero`, and `fall_sound`/`fall_complete` (a
  fall-through step agrees with `Region.Run` on the rest of the sequence).

These are graph facts, true by construction of `MStep` from `entry`/`labels`/`resolveT`.
Adequacy of the machine for `Region.Run` and Core 3.0 is the next obligation, not claimed here.
-/

namespace Silmaril.Wasm.Cfg.Machine

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H} {body : Expr}

theorem mstep_from_block {st st' : MState H} (h : MStep P host body st st') :
    ∃ b, st.node = .block b :=
  Proofs.Machine.mstep_from_block h

/-- **Every machine step follows an edge of the extracted block CFG**, or is a trap of the
block's body. -/
theorem mstep_edge {st st' : MState H} (h : MStep P host body st st') {b : BlockId}
    (hn : st.node = .block b) : Edge body b st'.node ∨ st'.node = .trap :=
  Proofs.Machine.mstep_edge h hn

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
    (hX' : codeAt body ⟨b.seq ++ [(b.idx, 0)], 0⟩ us (⟨t₂.length, ws, false, false, []⟩ :: ls) =
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
      (⟨labelArity loop t₁ t₂, ws, loop, tryT, cs⟩ :: ls) = some X')
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
same final store and frame. Under a handler frame the region semantics may catch, which the
machine does not model yet. -/
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
    (hL : ls[l.toNat]? = some L) (harity : L.arity ≤ stk₁.length) (hloop : L.loop = false)
    (hlev : levelLoop body b.seq.reverse l.toNat = false)
    (hX : codeAt body b stk ls = some X)
    (hY : codeOf body (goto (resolveT (labels body b.seq) l) (b.seq.length - (l.toNat + 1))
      (ls.drop (l.toNat + 1)) (L.outer ++ stk₁.drop (stk₁.length - L.arity)) s₁ f₁) = some Y)
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
    (hk : k ≠ 0) (hL : ls[l.toNat]? = some L) (harity : L.arity ≤ stk₁.length)
    (hloop : L.loop = false) (hlev : levelLoop body b.seq.reverse l.toNat = false)
    (hX : codeAt body b stk ls = some X)
    (hY : codeOf body (goto (resolveT (labels body b.seq) l) (b.seq.length - (l.toNat + 1))
      (ls.drop (l.toNat + 1)) (L.outer ++ stk₁.drop (stk₁.length - L.arity)) s₁ f₁) = some Y)
    {o : Region.Out} {s₂ : Store H} {f₂ : Frame} :
    Region.Run P host s₁ f₁ [] Y s₂ f₂ o → Region.Run P host s f [] X s₂ f₂ o :=
  Proofs.Machine.brIfTaken_step_sound hb ht hr hk hL harity hloop hlev hX hY

end Silmaril.Wasm.Cfg.Machine
