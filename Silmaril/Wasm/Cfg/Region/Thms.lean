module

public import Silmaril.Wasm.Cfg.Region.Defs
public import Silmaril.Wasm.Cfg.Block.Defs
import Silmaril.Proofs.Wasm.Cfg.Region
import Silmaril.Proofs.Wasm.Cfg.RegionDiv
import Silmaril.Proofs.Wasm.Cfg.RegionAtom
import Silmaril.Proofs.Wasm.Cfg.RegionBlocks

@[expose] public section

/-!
# The region semantics is adequate for Core 3.0

All results hold for every profile `P` and every host `host`. Proofs are in
`Silmaril.Proofs.Wasm.Cfg.Region`.

* **`run_adequate`**: on fragment code, a region run to `(s', f', o)` exists **iff** Core 3.0
  runs `vals vs ++ code` to a final form of `o` in store `s'` and frame `f'`. Soundness
  (`run_sound`) needs no fragment hypothesis. Completeness (`run_complete`) is proved by
  *expansion*: a region run of a Core successor is a region run of its predecessor
  (`run_expand`). That proof uses the Core inversions of `Execution.Core.Inversion` and the
  straight-line step classification of `Cfg.Exec`. No determinism is assumed, so every
  non-deterministic Core run is covered.
* **Compositionality**:
  * sequencing: `run_append_iff`, through `Then`;
  * values push: `run_vals_iff`;
  * structured instructions: by the rules of `Run` themselves, `block`, `loop`, `if` and the
    label continuation.
* `body_adequate`: the statement for a source body (`expression is`).
* **`frame_adequate`**: the same for a `FRAME` around fragment code (function bodies), to
  results.

* **Divergence**: `RunDiv` is the greatest fixed point of `DivF`, defined structurally with no
  appeal to Core divergence. `div_sound` needs no hypothesis. `div_complete` and
  `div_adequate` take the named atomic obligation `AtomTerm`: every non-control
  instruction's own Core reduction has no infinite run. Stuck states are leaves; this is
  not a claim of reaching a value or trap. `atomTerm` proves it for every profile and host
  (ranks on expansion level and the `fill`/`copy`/`init` counts), so **`div_iff`** is
  unconditional.

* **Calls** (`RunC P host C`): `call x` is answered by an oracle `C : Abstract.CallRel H`, in
  `EvalO`'s convention: arguments in parameter order, the callee's `Flow` results top first.
  `Run P host = RunC P host noCall` is the call-free semantics, and every statement above is
  about it. `run_soundC` holds under the named hypothesis `CallSound P host C`. Not yet:
  `CallSound` for `Abstract.closedCall`, completeness with calls, `call_ref`/`call_indirect`.

* **Tail calls**: `return_call*` end a region in a pending tail call (`Out.tail`, `Out.tailNull`,
  the final forms `vals vs ++ REF.FUNC_ADDR a :: c :: rest` and its null analogue), which needs
  no oracle; `run_sound` and `run_soundC` cover them. They are outside the fragment, so the
  adequacy statements above are unchanged.
-/

namespace Silmaril.Wasm.Cfg.Region

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H} {s s' : Store H} {f f' : Frame}

/-- **Soundness**: a region run is a Core 3.0 run to a final form of its outcome. -/
theorem run_sound {vs : List Val} {code : List Admin} {o : Out}
    (h : Run P host s f vs code s' f' o) :
    ∃ c', Steps P host ⟨s, f, vals vs ++ code⟩ ⟨s', f', c'⟩ ∧ o.Ends c' :=
  Proofs.Region.sound h

/-- **Soundness with calls**: with calls answered by an oracle `C` that is Core-sound
(`CallSound`, a named hypothesis), a region run is a Core 3.0 run to a final form of its
outcome. -/
theorem run_soundC {C : Abstract.CallRel H} (hC : CallSound P host C) {vs : List Val}
    {code : List Admin} {o : Out} (h : RunC P host C s f vs code s' f' o) :
    ∃ c', Steps P host ⟨s, f, vals vs ++ code⟩ ⟨s', f', c'⟩ ∧ o.Ends c' :=
  Proofs.Region.soundC hC h

/-- **Completeness**: every Core 3.0 run of fragment code to a final form is a region run. -/
theorem run_complete {code c' : List Admin} {o : Out} (hF : Frag code)
    (h : Steps P host ⟨s, f, code⟩ ⟨s', f', c'⟩) (he : o.Ends c') :
    Run P host s f [] code s' f' o :=
  Proofs.Region.complete hF h he

/-- **Expansion**: a Core step of fragment code stays in the fragment, and region runs of the
successor are region runs of the predecessor. -/
theorem run_expand {c c₁ : Config H} (h : Step P host c c₁) (hF : Frag c.code) :
    Frag c₁.code ∧ ∀ {vs : List Val} {s' : Store H} {f' : Frame} {o : Out},
      Run P host c₁.store c₁.frame vs c₁.code s' f' o →
        Run P host c.store c.frame vs c.code s' f' o :=
  Proofs.Region.expand h hF

/-- **Adequacy** of the region semantics for Core 3.0 on the fragment. -/
theorem run_adequate {vs : List Val} {code : List Admin} {o : Out} (hF : Frag code) :
    Run P host s f vs code s' f' o ↔
      ∃ c', Steps P host ⟨s, f, vals vs ++ code⟩ ⟨s', f', c'⟩ ∧ o.Ends c' :=
  Proofs.Region.adequate hF

/-- Adequacy for a source body. -/
theorem body_adequate {vs : List Val} {is : List Instr} {o : Out} (hF : ∀ i ∈ is, FragI i) :
    Run P host s f vs (expression is) s' f' o ↔
      ∃ c', Steps P host ⟨s, f, vals vs ++ expression is⟩ ⟨s', f', c'⟩ ∧ o.Ends c' :=
  Proofs.Region.adequate (Proofs.Region.frag_expression hF)

/-- **Sequencing**: a run of `A ++ B` is a run of `A` followed, on fall-through, by a run of
`B`. -/
theorem run_append_iff {vs : List Val} {A B : List Admin} {o : Out} :
    Run P host s f vs (A ++ B) s' f' o ↔
      ∃ s₁ f₁ o₁, Run P host s f vs A s₁ f₁ o₁ ∧ Then P host s₁ f₁ o₁ B s' f' o :=
  ⟨fun h => Proofs.Region.run_split h rfl,
    fun ⟨_, _, _, h₁, h₂⟩ => Proofs.Region.run_append h₁ h₂⟩

/-- Values in the code are pushed on the stack. -/
theorem run_vals_iff {vs ws : List Val} {code : List Admin} {o : Out} :
    Run P host s f vs (vals ws ++ code) s' f' o ↔ Run P host s f (vs ++ ws) code s' f' o :=
  Proofs.Region.run_vals_iff

/-- A source body under its function label is fragment code. -/
theorem frag_body {m : Nat} {body : List Instr} (hF : ∀ i ∈ body, FragI i) :
    Frag [.label m [] (expression body)] := by
  intro a ha
  simp only [List.mem_singleton] at ha
  subst ha
  exact .label (by simp) (Proofs.Region.frag_expression hF)

/-- **Frames**: a `FRAME_n{fi}` of fragment code runs to a result exactly when its body has a
region run, in the frame's own frame `fi`, whose outcome the frame returns (`FrameOut`). The
outer frame is unchanged. With `inner = [LABEL_n{} (expression body)]` (`frag_body`), this is
the code `call_ref` enters (`Step.callRef_wasm_inv_exact`). -/
theorem frame_adequate {fi : Frame} {n : Nat} {inner c' : List Admin} (hF : Frag inner)
    (hc : ∃ r : Result, c' = r.toAdmin) :
    Steps P host ⟨s, f, [.frame n fi inner]⟩ ⟨s', f', c'⟩ ↔
      f' = f ∧ ∃ fi' o, Run P host s fi [] inner s' fi' o ∧ FrameOut n o c' := by
  constructor
  · exact fun h => Proofs.Region.frame_complete hF h hc
  · rintro ⟨rfl, fi', o, h, ho⟩
    exact Proofs.Region.frame_sound h ho

/-! ## Divergence -/

/-- **Divergence soundness** (no hypothesis): a diverging region run is an infinite Core 3.0
run. -/
theorem div_sound {vs : List Val} {code : List Admin} (h : RunDiv P host s f vs code) :
    Diverges P host ⟨s, f, vals vs ++ code⟩ :=
  Proofs.Region.div_sound h

/-- **Divergence completeness**, given the named atomic obligation `AtomTerm`: every infinite
Core 3.0 run of fragment code is a diverging region run. -/
theorem div_complete {vs : List Val} {code : List Admin} (hA : AtomTerm P host)
    (hF : Frag code) (hd : Diverges P host ⟨s, f, vals vs ++ code⟩) :
    RunDiv P host s f vs code :=
  Proofs.Region.div_complete hA hF hd

/-- **Divergence adequacy**, given `AtomTerm`. -/
theorem div_adequate {vs : List Val} {code : List Admin} (hA : AtomTerm P host)
    (hF : Frag code) : RunDiv P host s f vs code ↔ Diverges P host ⟨s, f, vals vs ++ code⟩ :=
  Proofs.Region.div_adequate hA hF

/-- **The atomic obligation holds**: the Core 3.0 reduction of every non-control instruction,
from any values, store and frame, has no infinite run (strong normalisation; a stuck state
is a leaf, not a result). The measure is the instruction's expansion level plus, for the bulk
`fill`/`copy`/`init` instructions of memories, tables and arrays, the count operand. Every
profile and host. -/
theorem atomTerm : AtomTerm P host := Proofs.Region.atom_term

/-- **Divergence adequacy, unconditional**: on fragment code, a diverging region run exists
iff Core 3.0 diverges. -/
theorem div_iff {vs : List Val} {code : List Admin} (hF : Frag code) :
    RunDiv P host s f vs code ↔ Diverges P host ⟨s, f, vals vs ++ code⟩ :=
  Proofs.Region.div_adequate atomTerm hF

/-! ## Basic blocks -/

/-- **A sequence runs exactly along its canonical basic blocks** (`Cfg.segment`, the blocks of
the extracted block CFG): each block runs in turn, falling through to the next with the values it
leaves, until a block's outcome (branch, return, trap or exception, from its terminator) ends
the sequence. -/
theorem run_iff_blocks {is : List Instr} {vs : List Val} {o : Out} :
    Run P host s f vs (expression is) s' f' o ↔ SegRun P host s f vs (segment is) s' f' o :=
  Proofs.Region.run_iff_blocks

end Silmaril.Wasm.Cfg.Region
