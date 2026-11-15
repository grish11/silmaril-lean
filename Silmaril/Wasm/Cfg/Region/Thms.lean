module

public import Silmaril.Wasm.Cfg.Region.Defs
public import Silmaril.Wasm.Cfg.Block.Defs
import Silmaril.Proofs.Wasm.Cfg.Region
import Silmaril.Proofs.Wasm.Cfg.RegionDiv
import Silmaril.Proofs.Wasm.Cfg.RegionAtom
import Silmaril.Proofs.Wasm.Cfg.RegionBlocks
import Silmaril.Proofs.Wasm.Cfg.RegionTail
import Silmaril.Proofs.Wasm.Cfg.CallTransport
import Silmaril.Proofs.Wasm.Cfg.RegionTailRes
import Silmaril.Proofs.Wasm.Cfg.CtxSplit
import Silmaril.Proofs.Wasm.Cfg.CallSeq
import Silmaril.Proofs.Wasm.Cfg.RegionCallComplete
import Silmaril.Proofs.Wasm.Cfg.RegionDivC
public import Silmaril.Wasm.Abstract.CallX.Defs

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
  unconditional. `RunDiv` is `RunDivC` with no call answered (`noCall`) or diverging (`noDiv`).

* **Divergence with calls** (`RunDivC P host C D`): a direct call is answered by `C` with values
  and the continuation diverges, or `D` names it (it diverges inside the callee).
  `div_soundC` under `CallSound` and `DivCallSound`; **`div_completeC`**: on code of the
  fragment with calls (`FragC`), a diverging Core run is a `RunDivC` run under complete `C` and
  `D` (`CallCompleteG`, `DivCallComplete`) whose guard holds at every call the run reaches
  (`GuardedCalls`). At a call, the run diverges in the callee (through any chain of tail calls
  out of its frame) or returns and the continuation diverges.

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

/-- **Expansion in the fragment with calls** (`FragB cf`, `cf = true` allowing direct calls),
for any call oracle: a Core step whose redex is not a direct call (`¬ CallAt`)
stays in the fragment, and region runs of the successor are region runs of the predecessor. -/
theorem run_expandB {cf : Bool} {C : Abstract.CallRel H} {c c₁ : Config H}
    (h : Step P host c c₁) (hF : FragB cf c.code) (hnc : ¬ CallAt c.code) :
    FragB cf c₁.code ∧ ∀ {vs : List Val} {s' : Store H} {f' : Frame} {o : Out},
      RunC P host C c₁.store c₁.frame vs c₁.code s' f' o →
        RunC P host C c.store c.frame vs c.code s' f' o :=
  Proofs.Region.expandB h hF hnc

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

/-- **Divergence soundness with calls**: when `C` answers calls as Core runs them and the calls
`D` names diverge in Core, a diverging region run with calls is an infinite Core 3.0 run. -/
theorem div_soundC {C : Abstract.CallRel H} {D : Store H → Nat → List Val → Prop}
    (hC : CallSound P host C) (hD : DivCallSound P host D) {vs : List Val} {code : List Admin}
    (h : RunDivC P host C D s f vs code) : Diverges P host ⟨s, f, vals vs ++ code⟩ :=
  Proofs.Region.div_soundC hC hD h

/-- **Divergence completeness with direct calls**: under a complete oracle `C` and a complete
divergence predicate `D`, their guard `G` holding at every call the run reaches, every infinite
Core 3.0 run of code of the fragment with calls (`FragC`) is a diverging region run with calls. -/
theorem div_completeC {G : Store H → Nat → List Val → Prop} {C : Abstract.CallRel H}
    {D : Store H → Nat → List Val → Prop} (hC : CallCompleteG P host G C)
    (hD : DivCallComplete P host G D) {vs : List Val} {code : List Admin} (hF : FragC code)
    (hG : GuardedCalls P host G ⟨s, f, vals vs ++ code⟩)
    (hd : Diverges P host ⟨s, f, vals vs ++ code⟩) : RunDivC P host C D s f vs code :=
  Proofs.Region.div_completeC atomTerm hC hD hF hG hd

/-! ## Basic blocks -/

/-- **A sequence runs exactly along its canonical basic blocks** (`Cfg.segment`, the blocks of
the extracted block CFG): each block runs in turn, falling through to the next with the values it
leaves, until a block's outcome (branch, return, trap or exception, from its terminator) ends
the sequence. -/
theorem run_iff_blocks {is : List Instr} {vs : List Val} {o : Out} :
    Run P host s f vs (expression is) s' f' o ↔ SegRun P host s f vs (segment is) s' f' o :=
  Proofs.Region.run_iff_blocks

/-! ## Tail calls at the frame -/

/-- An oracle sound for every `call_ref` form is sound for `call`. -/
theorem callSound_of_callSoundA {C : Abstract.CallRel H} (h : CallSoundA P host C) :
    CallSound P host C :=
  Proofs.Region.callSound_of_A h

/-- **A pending tail call is completed by the frame** (frame replacement): a frame whose body
ends in a pending tail call of the function at `a` runs, as Core leaves the frame and calls the
callee on the top `ps.length` values (`return_call_ref-frame-addr`), to the oracle's answer for
that call: the callee's top `rs.length` results, its trap or its exception, in the callee's final
store and the outer frame. Under the named hypothesis `CallSoundA`. -/
theorem frame_tail_sound {C : Abstract.CallRel H} (hC : CallSoundA P host C) {s₂ s₃ : Store H}
    {fi fi₂ : Frame} {n : Nat} {inner : List Admin} {W W₀ args : List Val} {a : Nat} {c : Admin}
    {fn : FuncInst H} {ps rs : List Validation.CValType} {fl : Binaryen.Flow}
    (h : RunC P host C s fi [] inner s₂ fi₂ (.tail W a c))
    (hfn : s₂.funcs[a]? = some fn) (hty : Validation.DefType.funcType? fn.type = some (ps, rs))
    (hW : W = W₀ ++ args) (hn : args.length = ps.length) (hcall : C s₂ a args (s₃, fl)) :
    (∀ vs, fl.retVals = some vs → Steps P host ⟨s, f, [.frame n fi inner]⟩
        ⟨s₃, f, vals (vs.take rs.length).reverse⟩) ∧
    (fl = .trap → Steps P host ⟨s, f, [.frame n fi inner]⟩ ⟨s₃, f, [.trap]⟩) ∧
    (∀ t, fl = .throw t → Steps P host ⟨s, f, [.frame n fi inner]⟩ ⟨s₃, f, throwing t⟩) :=
  Proofs.Region.frame_tail_sound hC h hfn hty hW hn hcall

/-! ## Calls from Core runs -/

/-- **A complete oracle turns a Core call into a region call**: under `CallCompleteG` (a named
hypothesis, guarded by `G`), a Core run of the callee of `call x` to a result ends in the caller's
frame, and `call x` runs as `RunC.call` (continuing on the results), `RunC.callTrap` or
`RunC.callThrow`. -/
theorem call_of_core {C : Abstract.CallRel H} {G : Store H → Nat → List Val → Prop}
    (hC : CallCompleteG P host G C) {s₁ : Store H} {f₁ : Frame} {ws us : List Val} {x : FuncIdx}
    {a : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType} {code : List Admin}
    {r : Result} (hfi : s.func? f x = some (a, fi))
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hn : us.length = ps.length)
    (hG : G s a us)
    (hs : Steps P host ⟨s, f, vals us ++ [.ref (.func a), .callRefType fi.type]⟩
      ⟨s₁, f₁, r.toAdmin⟩) :
    f₁ = f ∧
      (∀ vs, r = .values vs → ∀ {s' : Store H} {f' : Frame} {o : Out},
        RunC P host C s₁ f (ws ++ vs) code s' f' o →
          RunC P host C s f (ws ++ us) (.plain (.call x) :: code) s' f' o) ∧
      (r = .trap → RunC P host C s f (ws ++ us) (.plain (.call x) :: code) s₁ f .trap) ∧
      (∀ t, r = .throw t →
        RunC P host C s f (ws ++ us) (.plain (.call x) :: code) s₁ f (.throw t)) :=
  Proofs.Region.call_of_core hC hfi hty hn hG hs

/-! ## Tail calls resolved as `CallX` resolves them -/

/-- **The region semantics resolves tail calls as `Abstract.CallX.TailRes` does**: a tail call
that `TailRes` resolves to the callee `a` (on the stack `stk`, top first; `return_call`,
`return_call_indirect` through the table and the cast, `return_call_ref`) runs to a pending tail
call of `a` over the values `W` under its operands. -/
theorem run_of_tailRes {C : Abstract.CallRel H} {i : Instr} {stk : List Val} {a : Nat}
    (W : List Val)
    (h : Abstract.CallX.TailRes s f i stk (some (a, stk.drop (Abstract.CallX.tailPop i)))) :
    ∃ c, c.IsReturnCallRef ∧ RunC P host C s f (W ++ (stk.take (Abstract.CallX.tailPop i)).reverse)
      [.plain i] s f (.tail W a c) :=
  Proofs.Region.run_of_tailRes W h

/-- An unresolved tail call (`TailRes … none`) traps, or is a pending tail call of null. -/
theorem run_of_tailRes_none {C : Abstract.CallRel H} {i : Instr} {stk : List Val}
    (W : List Val) (h : Abstract.CallX.TailRes s f i stk none) :
    RunC P host C s f (W ++ (stk.take (Abstract.CallX.tailPop i)).reverse) [.plain i] s f .trap ∨
      ∃ c, c.IsReturnCallRef ∧ RunC P host C s f
        (W ++ (stk.take (Abstract.CallX.tailPop i)).reverse) [.plain i] s f (.tailNull W c) :=
  Proofs.Region.run_of_tailRes_none W h

/-! ## Handler clauses -/

/-- **`Catches` is Core's handler resolution**: a handler around a thrown exception runs, in
Core 3.0, to the first matching clause's branch with the values it pushes
(`vals us ++ [br l]`, values bottom first: the exception's fields in tag order, then
`ref.exn a` for `catch_ref`/`catch_all_ref`), or rethrows when no clause matches. -/
theorem catches_steps {a n : Nat} {cs : List Catch} {us : List Val} {l : LabelIdx}
    (hc : Catches s f a cs (some (us, l))) :
    Steps P host ⟨s, f, [.handler n cs (throwing a)]⟩ ⟨s, f, vals us ++ [.plain (.br l)]⟩ :=
  Proofs.Region.catches_steps (r := some (us, l)) hc

/-- No clause matches: the handler rethrows. -/
theorem catches_steps_none {a n : Nat} {cs : List Catch} (hc : Catches s f a cs none) :
    Steps P host ⟨s, f, [.handler n cs (throwing a)]⟩ ⟨s, f, throwing a⟩ :=
  Proofs.Region.catches_steps (r := none) hc

/-- Every clause list resolves an exception (first match, or none). -/
theorem catches_total (s : Store H) (f : Frame) (a : Nat) (cs : List Catch) :
    ∃ r, Catches s f a cs r :=
  Proofs.Region.catches_total s f a cs

/-- The resolution is unique (first match). -/
theorem catches_unique {a : Nat} {cs : List Catch} {r r' : Option (List Val × LabelIdx)}
    (h : Catches s f a cs r) (h' : Catches s f a cs r') : r = r' :=
  Proofs.Region.catches_unique h h'

/-! ## Runs through a context in a sequence -/

/-- **The first exit of a frame in a sequence** (every profile and host): a Core run of
`vals ws ++ FRAME_n{F} X :: rest` to a code with no `FRAME_n` at its top first runs `X` alone, in
its own frame, then leaves the frame by a Core exit rule (`FrameExit`), and the sequence
continues from `vals ws ++ out ++ rest`. -/
theorem frame_seq_exit {ws : List Val} {n : Nat} {F : Frame} {X rest : List Admin}
    {c' : Config H} (h : Steps P host ⟨s, f, vals ws ++ .frame n F X :: rest⟩ c')
    (hfin : ∀ F' X', Admin.frame n F' X' ∉ c'.code) :
    ∃ (s₁ : Store H) (F₁ : Frame) (X₁ out : List Admin),
      Steps P host ⟨s, F, X⟩ ⟨s₁, F₁, X₁⟩ ∧ FrameExit s₁ F₁ n X₁ out ∧
      Steps P host ⟨s₁, f, vals ws ++ out ++ rest⟩ c' :=
  Proofs.Region.frame_seq_exit h s f F X rfl hfin

/-- **The first exit of a handler in a sequence** (`HandlerExit`, catching included). -/
theorem handler_seq_exit {ws : List Val} {n : Nat} {cs : List Catch} {X rest : List Admin}
    {c' : Config H} (h : Steps P host ⟨s, f, vals ws ++ .handler n cs X :: rest⟩ c')
    (hfin : ∀ X', Admin.handler n cs X' ∉ c'.code) :
    ∃ (s₁ : Store H) (f₁ : Frame) (X₁ out : List Admin),
      Steps P host ⟨s, f, X⟩ ⟨s₁, f₁, X₁⟩ ∧ HandlerExit s₁ f₁ n cs X₁ out ∧
      Steps P host ⟨s₁, f₁, vals ws ++ out ++ rest⟩ c' :=
  Proofs.Region.handler_seq_exit h s f X rfl hfin

/-- **The first exit of a label in a sequence** (`LabelExit`). -/
theorem label_seq_exit {ws : List Val} {n : Nat} {cont : List Instr} {X rest : List Admin}
    {c' : Config H} (h : Steps P host ⟨s, f, vals ws ++ .label n cont X :: rest⟩ c')
    (hfin : ∀ X', Admin.label n cont X' ∉ c'.code) :
    ∃ (s₁ : Store H) (f₁ : Frame) (X₁ out : List Admin),
      Steps P host ⟨s, f, X⟩ ⟨s₁, f₁, X₁⟩ ∧ LabelExit n cont X₁ out ∧
      Steps P host ⟨s₁, f₁, vals ws ++ out ++ rest⟩ c' :=
  Proofs.Region.label_seq_exit h s f X rfl hfin

/-- **A frame in a sequence runs to a result, or leaves by a tail call**: the frame alone runs
in the outer frame to a result `r` and the sequence continues from `vals ws ++ r ++ rest`, or it
is left by `return_call_ref-frame-addr` to a `call_ref` of `a` on `args`. -/
theorem frame_seq_result {ws : List Val} {n : Nat} {F : Frame} {X rest : List Admin}
    {c' : Config H} (h : Steps P host ⟨s, f, vals ws ++ .frame n F X :: rest⟩ c')
    (hfin : ∀ F' X', Admin.frame n F' X' ∉ c'.code) :
    (∃ (s₁ : Store H) (r : Result), Steps P host ⟨s, f, [.frame n F X]⟩ ⟨s₁, f, r.toAdmin⟩ ∧
        Steps P host ⟨s₁, f, vals ws ++ r.toAdmin ++ rest⟩ c') ∨
      ∃ (s₁ : Store H) (args : List Val) (a : Nat) (c : Admin), c.IsCallRef ∧
        Steps P host ⟨s, f, [.frame n F X]⟩ ⟨s₁, f, vals args ++ [.ref (.func a), c]⟩ ∧
        Steps P host ⟨s₁, f, vals ws ++ (vals args ++ [.ref (.func a), c]) ++ rest⟩ c' :=
  Proofs.Region.frame_seq_result h hfin

/-- **A frame in a sequence is still running, or has exited** (every profile and host). -/
theorem frame_seq_cases {ws : List Val} {n : Nat} {F : Frame} {X rest : List Admin}
    {c' : Config H} (h : Steps P host ⟨s, f, vals ws ++ .frame n F X :: rest⟩ c') :
    (∃ F' X', c' = ⟨c'.store, f, vals ws ++ .frame n F' X' :: rest⟩ ∧
        Steps P host ⟨s, F, X⟩ ⟨c'.store, F', X'⟩) ∨
      ∃ (s₁ : Store H) (F₁ : Frame) (X₁ out : List Admin),
        Steps P host ⟨s, F, X⟩ ⟨s₁, F₁, X₁⟩ ∧ FrameExit s₁ F₁ n X₁ out ∧
        Steps P host ⟨s₁, f, vals ws ++ out ++ rest⟩ c' :=
  Proofs.Region.frame_seq_cases h s f F X rfl

/-- **A direct call under values, run alone** (every profile and host, Wasm callees): every
Core run of `vals vs ++ [call x]` is still at the call, at the resolved `call_ref`, inside the
callee's frame on the top `ps.length` values `us` (`vs = ws ++ us`), or past the frame's first
exit (`FrameExit`), in which case the callee's `call_ref` itself runs to the exit's code and the
run continues from `vals ws ++ out`. -/
theorem call_vals_cases {vs : List Val} {x : FuncIdx} {c : Config H}
    (hw : ∀ fi ∈ s.funcs, ∃ fn, fi.code = .wasm fn)
    (h : Steps P host ⟨s, f, vals vs ++ [.plain (.call x)]⟩ c) :
    c = ⟨s, f, vals vs ++ [.plain (.call x)]⟩ ∨
    ∃ a fi, f.module.funcs[x.toNat]? = some a ∧ s.funcs[a]? = some fi ∧
      (c = ⟨s, f, vals vs ++ [.ref (.func a), .callRefType fi.type]⟩ ∨
        ∃ (ws us : List Val) (ps rs : Validation.Ty (.list .val)) (code : Func),
          vs = ws ++ us ∧ fi.code = .wasm code ∧ Validation.Expand fi.type (.func ps rs) ∧
          us.length = ps.length ∧
          ((∃ F' X', c = ⟨c.store, f, vals ws ++ [.frame rs.length F' X']⟩ ∧
              Steps P host ⟨s, Frame.forCall fi.module us code.locals,
                [.label rs.length [] (expression code.body)]⟩ ⟨c.store, F', X'⟩) ∨
            ∃ (s₁ : Store H) (F₁ : Frame) (X₁ out : List Admin),
              FrameExit s₁ F₁ rs.length X₁ out ∧
              Steps P host ⟨s, f, vals us ++ [.ref (.func a), .callRefType fi.type]⟩
                ⟨s₁, f, out⟩ ∧
              Steps P host ⟨s₁, f, vals ws ++ out⟩ c)) :=
  Proofs.Region.call_vals_cases hw h

/-! ## Direct calls, from Core runs to region runs -/

/-- **A direct call in a sequence, run to a final form** (every profile and host, Wasm and host
callees): the call resolves its callee `a`, whose `call_ref` runs on the top `ps.length` values
`us` to a result `r` in the caller's frame (tail calls out of the callee's frame followed), and the
sequence continues from `vals ws' ++ r ++ rest`. -/
theorem call_seq_result {ws : List Val} {x : FuncIdx} {rest : List Admin} {c' : Config H}
    (hfin : ∃ o : Out, o.Ends c'.code)
    (h : Steps P host ⟨s, f, vals ws ++ .plain (.call x) :: rest⟩ c') :
    ∃ (a : Nat) (fi : FuncInst H), f.module.funcs[x.toNat]? = some a ∧ s.funcs[a]? = some fi ∧
      ∃ (ws' us : List Val) (ps rs : Validation.Ty (.list .val)) (s₁ : Store H) (r : Result),
        ws = ws' ++ us ∧ Validation.Expand fi.type (.func ps rs) ∧ us.length = ps.length ∧
        Steps P host ⟨s, f, vals us ++ [.ref (.func a), .callRefType fi.type]⟩ ⟨s₁, f, r.toAdmin⟩ ∧
        Steps P host ⟨s₁, f, vals ws' ++ r.toAdmin ++ rest⟩ c' :=
  Proofs.Region.call_seq_result hfin h

/-- **A direct call, from Core to `RunC`** (every profile and host): under a complete oracle
(`CallCompleteG`, its guard holding at the call's store), a Core run of
`vals ws ++ call x :: rest` to a final form of `o` is a `RunC` run of `call x :: rest`, given that
the continuation after the callee's values is one (`hk`). -/
theorem run_call_complete {G : Store H → Nat → List Val → Prop} {C : Abstract.CallRel H}
    (hC : CallCompleteG P host G C) {ws : List Val} {x : FuncIdx} {rest c' : List Admin} {o : Out}
    (hG : ∀ a us, G s a us)
    (h : Steps P host ⟨s, f, vals ws ++ .plain (.call x) :: rest⟩ ⟨s', f', c'⟩) (ho : o.Ends c')
    (hk : ∀ (s₁ : Store H) (ws' vs : List Val),
      Steps P host ⟨s₁, f, vals (ws' ++ vs) ++ rest⟩ ⟨s', f', c'⟩ →
        RunC P host C s₁ f (ws' ++ vs) rest s' f' o) :
    RunC P host C s f ws (.plain (.call x) :: rest) s' f' o :=
  Proofs.Region.run_call_complete hC hG h ho hk

/-- **A Core-answered call is a region-run inclusion** (every outcome): when the callee's
`call_ref` on the top values `us` runs in Core to `r` and a complete oracle answers it, every
`RunC` run of `vals ws ++ r ++ rest` is one of `vals (ws ++ us) ++ call x :: rest`. With
`label_back`/`handler_back` it lifts through labels and handlers. -/
theorem call_incl {G : Store H → Nat → List Val → Prop} {C : Abstract.CallRel H}
    (hC : CallCompleteG P host G C) {s₁ : Store H} {ws us : List Val} {x : FuncIdx} {a : Nat}
    {fi : FuncInst H} {ps rs : Validation.Ty (.list .val)} {rest : List Admin} {r : Result}
    (hx : f.module.funcs[x.toNat]? = some a) (hfi : s.funcs[a]? = some fi)
    (he : Validation.Expand fi.type (.func ps rs)) (hn : us.length = ps.length) (hG : G s a us)
    (hcall : Steps P host ⟨s, f, vals us ++ [.ref (.func a), .callRefType fi.type]⟩
      ⟨s₁, f, r.toAdmin⟩) {o : Out} {s₂ : Store H} {f₂ : Frame}
    (hr : RunC P host C s₁ f [] (vals ws ++ r.toAdmin ++ rest) s₂ f₂ o) :
    RunC P host C s f [] (vals (ws ++ us) ++ .plain (.call x) :: rest) s₂ f₂ o :=
  Proofs.Region.call_incl hC hx hfi he hn hG hcall hr

/-! ## Core completeness with direct calls -/

/-- **Core completeness for code with direct calls** (every profile and host): under a complete
oracle (`CallCompleteG`) whose guard holds at every call the run reaches (`GuardedCalls`), every
Core 3.0 run of code of the fragment with calls (`FragC`: direct calls anywhere, in blocks,
loops, `if`s, `try_table`s, labels and handlers) to a final form of `o` is a `RunC` run. -/
theorem run_completeC {G : Store H → Nat → List Val → Prop} {C : Abstract.CallRel H}
    (hC : CallCompleteG P host G C) {code c' : List Admin} {o : Out}
    (hG : GuardedCalls P host G ⟨s, f, code⟩) (hF : FragC code)
    (h : Steps P host ⟨s, f, code⟩ ⟨s', f', c'⟩) (he : o.Ends c') :
    RunC P host C s f [] code s' f' o :=
  Proofs.Region.completeC hC hG hF h he

end Silmaril.Wasm.Cfg.Region
