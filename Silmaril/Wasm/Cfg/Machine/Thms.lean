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

end Silmaril.Wasm.Cfg.Machine
