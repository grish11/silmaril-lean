module

public import Silmaril.Wasm.Cfg.Exec.Defs
public import Silmaril.Wasm.Execution.Core.Inversion.Defs

@[expose] public section

/-!
# A structured big-step semantics of Wasm regions, against Core 3.0

`Run P host s f vs code s' f' o` is a compositional big-step semantics of runtime code
`code` (Core 3.0 administrative instructions) with operand stack `vs` (bottom first). It
runs from store `s` and frame `f` to store `s'`, frame `f'` and outcome `o`:

* `normal vs'`: fell through, leaving the stack `vs'`;
* `br l vs'`: branching to the `l`-th enclosing label, with stack `vs'`;
* `ret vs'`: returning, with stack `vs'`;
* `trap`.

The rules follow the structure of the code:
* a value is pushed;
* a non-control instruction (`Det.famOf ≠ .control`: numeric, vector, variable, table,
  memory, reference, aggregate, parametric) runs by its own Core 3.0 reduction, to values
  or to a trap;
* `br_if` and `if` read their `i32` condition;
* `block`, `loop` and `if` push a `LABEL` exactly as Core does;
* a `LABEL` runs its body to an outcome and then continues according to it: fall through,
  run the continuation on a branch to the label itself, or pass an outer branch, a return or
  a trap outwards.

Outcomes carry values, store and frame, and every branch reads data.

The fragment (`Frag`) is call-free and exception-free: values, non-control instructions,
`block`, `loop`, `if`, `br`, `br_if`, `br_table`, `br_on_null`, `br_on_non_null`, `br_on_cast`,
`br_on_cast_fail`, `return`, `TRAP` and `LABEL`. On it the semantics is
**adequate in both directions** for every profile and host (`Region/Thms.lean`): `Run`
holds exactly when Core 3.0 runs the code to a final form of that outcome. This covers
terminating runs only; divergence is not treated yet.
-/

namespace Silmaril.Wasm.Cfg.Region

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

/-- How control leaves a region. -/
inductive Out where
  | normal (vs : List Val)
  | br (l : Nat) (vs : List Val)
  | ret (vs : List Val)
  | trap
  deriving DecidableEq, Repr

/-- The Core final forms of an outcome. Anything after a `br` or `return` is dead. -/
def Out.Ends : Out → List Admin → Prop
  | .normal vs, c => c = vals vs
  | .br l vs, c => ∃ (x : LabelIdx) (rest : List Admin), x.toNat = l ∧
      c = vals vs ++ .plain (.br x) :: rest
  | .ret vs, c => ∃ rest : List Admin, c = vals vs ++ .plain .return_ :: rest
  | .trap, c => c = [.trap]

/-- Source instructions of the fragment. -/
inductive FragI : Instr → Prop where
  | simple {i : Instr} (h : SingleThreaded.Det.famOf (.plain i) ≠ .control) : FragI i
  | const {i : Instr} (h : (Admin.plain i).val? ≠ none) : FragI i
  | block {bt : BlockType} {b : List Instr} (h : ∀ i ∈ b, FragI i) : FragI (.block bt b)
  | loop {bt : BlockType} {b : List Instr} (h : ∀ i ∈ b, FragI i) : FragI (.loop bt b)
  | if_ {bt : BlockType} {t e : List Instr} (ht : ∀ i ∈ t, FragI i) (he : ∀ i ∈ e, FragI i) :
      FragI (.if_ bt t e)
  | br (l : LabelIdx) : FragI (.br l)
  | brIf (l : LabelIdx) : FragI (.brIf l)
  | return_ : FragI .return_
  /-- `br_table`, `br_on_null`, `br_on_non_null`, `br_on_cast`, `br_on_cast_fail`. -/
  | brData {i : Instr} (h : i.IsBrData) : FragI i

/-- Runtime instructions of the fragment. -/
inductive FragA : Admin → Prop where
  | val {a : Admin} (h : a.val? ≠ none) : FragA a
  | plain {i : Instr} (h : FragI i) : FragA (.plain i)
  | trap : FragA .trap
  | label {n : Nat} {cont : List Instr} {inner : List Admin} (hc : ∀ i ∈ cont, FragI i)
      (hi : ∀ a ∈ inner, FragA a) : FragA (.label n cont inner)

/-- Runtime code of the fragment. -/
def Frag (code : List Admin) : Prop := ∀ a ∈ code, FragA a

variable {H : Type}

/-- **The region semantics.** -/
inductive Run (P : Profile) (host : HostSemantics H) :
    Store H → Frame → List Val → List Admin → Store H → Frame → Out → Prop where
  | nil {s : Store H} {f : Frame} {vs : List Val} : Run P host s f vs [] s f (.normal vs)
  | val {s s' : Store H} {f f' : Frame} {vs : List Val} {a : Admin} {v : Val}
      {code : List Admin} {o : Out} (hv : a.val? = some v)
      (h : Run P host s f (vs ++ [v]) code s' f' o) : Run P host s f vs (a :: code) s' f' o
  /-- A non-control instruction runs by Core reduction to values. -/
  | simple {s s₁ s' : Store H} {f f₁ f' : Frame} {vs vs₁ : List Val} {i : Instr}
      {code : List Admin} {o : Out} (hi : SingleThreaded.Det.famOf (.plain i) ≠ .control)
      (h₁ : Steps P host ⟨s, f, vals vs ++ [.plain i]⟩ ⟨s₁, f₁, vals vs₁⟩)
      (h : Run P host s₁ f₁ vs₁ code s' f' o) : Run P host s f vs (.plain i :: code) s' f' o
  /-- A non-control instruction traps. -/
  | simpleTrap {s s₁ : Store H} {f f₁ : Frame} {vs : List Val} {i : Instr} {code : List Admin}
      (hi : SingleThreaded.Det.famOf (.plain i) ≠ .control)
      (h₁ : Steps P host ⟨s, f, vals vs ++ [.plain i]⟩ ⟨s₁, f₁, [.trap]⟩) :
      Run P host s f vs (.plain i :: code) s₁ f₁ .trap
  | trap {s : Store H} {f : Frame} {vs : List Val} {code : List Admin} :
      Run P host s f vs (.trap :: code) s f .trap
  | br {s : Store H} {f : Frame} {vs : List Val} {l : LabelIdx} {code : List Admin} :
      Run P host s f vs (.plain (.br l) :: code) s f (.br l.toNat vs)
  | ret {s : Store H} {f : Frame} {vs : List Val} {code : List Admin} :
      Run P host s f vs (.plain .return_ :: code) s f (.ret vs)
  | brIf {s s' : Store H} {f f' : Frame} {ws : List Val} {k : BitVec 32} {l : LabelIdx}
      {code : List Admin} {o : Out}
      (h : Run P host s f ws ((if k = 0 then [] else [.plain (.br l)]) ++ code) s' f' o) :
      Run P host s f (ws ++ [.i32 k]) (.plain (.brIf l) :: code) s' f' o
  /-- A data-dependent branch reads its operands (`BrStep`). -/
  | brData {s s' : Store H} {f f' : Frame} {ws us us' : List Val} {i : Instr} {X : List Admin}
      {code : List Admin} {o : Out} (hb : BrStep s f us i us' X)
      (h : Run P host s f (ws ++ us') (X ++ code) s' f' o) :
      Run P host s f (ws ++ us) (.plain i :: code) s' f' o
  | block {s s' : Store H} {f f' : Frame} {ws us : List Val} {bt : BlockType} {b : List Instr}
      {t₁ t₂ : List CValType} {code : List Admin} {o : Out}
      (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : us.length = t₁.length)
      (h : Run P host s f ws (.label t₂.length [] (vals us ++ expression b) :: code) s' f' o) :
      Run P host s f (ws ++ us) (.plain (.block bt b) :: code) s' f' o
  | loop {s s' : Store H} {f f' : Frame} {ws us : List Val} {bt : BlockType} {b : List Instr}
      {t₁ t₂ : List CValType} {code : List Admin} {o : Out}
      (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : us.length = t₁.length)
      (h : Run P host s f ws (.label t₁.length [.loop bt b] (vals us ++ expression b) :: code)
        s' f' o) :
      Run P host s f (ws ++ us) (.plain (.loop bt b) :: code) s' f' o
  | if_ {s s' : Store H} {f f' : Frame} {ws : List Val} {k : BitVec 32} {bt : BlockType}
      {t e : List Instr} {code : List Admin} {o : Out}
      (h : Run P host s f ws (.plain (.block bt (if k = 0 then e else t)) :: code) s' f' o) :
      Run P host s f (ws ++ [.i32 k]) (.plain (.if_ bt t e) :: code) s' f' o
  /-- The label's body falls through: its values are pushed. -/
  | labelNormal {s s₁ s' : Store H} {f f₁ f' : Frame} {vs us : List Val} {n : Nat}
      {cont : List Instr} {inner code : List Admin} {o : Out}
      (hin : Run P host s f [] inner s₁ f₁ (.normal us))
      (h : Run P host s₁ f₁ (vs ++ us) code s' f' o) :
      Run P host s f vs (.label n cont inner :: code) s' f' o
  /-- The body branches to the label itself: the continuation runs on the top `n` values. -/
  | labelBr0 {s s₁ s' : Store H} {f f₁ f' : Frame} {vs us₁ us₂ : List Val} {n : Nat}
      {cont : List Instr} {inner code : List Admin} {o : Out}
      (hin : Run P host s f [] inner s₁ f₁ (.br 0 (us₁ ++ us₂))) (hn : us₂.length = n)
      (h : Run P host s₁ f₁ vs (vals us₂ ++ expression cont ++ code) s' f' o) :
      Run P host s f vs (.label n cont inner :: code) s' f' o
  | labelBrSucc {s s₁ : Store H} {f f₁ : Frame} {vs us : List Val} {n l : Nat}
      {cont : List Instr} {inner code : List Admin}
      (hin : Run P host s f [] inner s₁ f₁ (.br (l + 1) us)) :
      Run P host s f vs (.label n cont inner :: code) s₁ f₁ (.br l (vs ++ us))
  | labelRet {s s₁ : Store H} {f f₁ : Frame} {vs us : List Val} {n : Nat}
      {cont : List Instr} {inner code : List Admin}
      (hin : Run P host s f [] inner s₁ f₁ (.ret us)) :
      Run P host s f vs (.label n cont inner :: code) s₁ f₁ (.ret (vs ++ us))
  | labelTrap {s s₁ : Store H} {f f₁ : Frame} {vs : List Val} {n : Nat}
      {cont : List Instr} {inner code : List Admin}
      (hin : Run P host s f [] inner s₁ f₁ .trap) :
      Run P host s f vs (.label n cont inner :: code) s₁ f₁ .trap

/-- Sequencing: after a first part ends in state `s₁, f₁` with outcome `o₁`, the second part
`B` runs on fall-through; any other outcome skips `B`. -/
def Then (P : Profile) (host : HostSemantics H) (s₁ : Store H) (f₁ : Frame) :
    Out → List Admin → Store H → Frame → Out → Prop
  | .normal us, B, s', f', o => Run P host s₁ f₁ us B s' f' o
  | o₁, _, s', f', o => o = o₁ ∧ s' = s₁ ∧ f' = f₁

/-- What a `FRAME_n` returns for a body outcome. Falling through needs exactly `n` values; a
`return` keeps the top `n`. A branch out of the frame does not happen in validated code and
has no result. -/
def FrameOut (n : Nat) : Out → List Admin → Prop
  | .normal us, c => us.length = n ∧ c = vals us
  | .ret us, c => ∃ us₁ ws, us = us₁ ++ ws ∧ ws.length = n ∧ c = vals ws
  | .trap, c => c = [.trap]
  | .br _ _, _ => False

end Silmaril.Wasm.Cfg.Region

/-! ## Divergence -/

namespace Silmaril.Wasm.Cfg.Region

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type}

/-- One layer of a diverging region run, with the rest of the divergence in `R`. A label
diverges inside, or its body ends (a terminating `Run`) and the continuation diverges. Every
rule either takes at least one Core step or moves to a strictly smaller code (`val`,
`labelIn`). -/
inductive DivF (P : Profile) (host : HostSemantics H)
    (R : Store H → Frame → List Val → List Admin → Prop) :
    Store H → Frame → List Val → List Admin → Prop where
  | val {s : Store H} {f : Frame} {vs : List Val} {a : Admin} {v : Val} {code : List Admin}
      (hv : a.val? = some v) (h : R s f (vs ++ [v]) code) : DivF P host R s f vs (a :: code)
  | simple {s s₁ : Store H} {f f₁ : Frame} {vs vs₁ : List Val} {i : Instr} {code : List Admin}
      (hi : SingleThreaded.Det.famOf (.plain i) ≠ .control)
      (h₁ : Steps P host ⟨s, f, vals vs ++ [.plain i]⟩ ⟨s₁, f₁, vals vs₁⟩)
      (h : R s₁ f₁ vs₁ code) : DivF P host R s f vs (.plain i :: code)
  | brIf {s : Store H} {f : Frame} {ws : List Val} {k : BitVec 32} {l : LabelIdx}
      {code : List Admin} (h : R s f ws ((if k = 0 then [] else [.plain (.br l)]) ++ code)) :
      DivF P host R s f (ws ++ [.i32 k]) (.plain (.brIf l) :: code)
  | brData {s : Store H} {f : Frame} {ws us us' : List Val} {i : Instr} {X code : List Admin}
      (hb : BrStep s f us i us' X) (h : R s f (ws ++ us') (X ++ code)) :
      DivF P host R s f (ws ++ us) (.plain i :: code)
  | block {s : Store H} {f : Frame} {ws us : List Val} {bt : BlockType} {b : List Instr}
      {t₁ t₂ : List CValType} {code : List Admin}
      (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : us.length = t₁.length)
      (h : R s f ws (.label t₂.length [] (vals us ++ expression b) :: code)) :
      DivF P host R s f (ws ++ us) (.plain (.block bt b) :: code)
  | loop {s : Store H} {f : Frame} {ws us : List Val} {bt : BlockType} {b : List Instr}
      {t₁ t₂ : List CValType} {code : List Admin}
      (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : us.length = t₁.length)
      (h : R s f ws (.label t₁.length [.loop bt b] (vals us ++ expression b) :: code)) :
      DivF P host R s f (ws ++ us) (.plain (.loop bt b) :: code)
  | if_ {s : Store H} {f : Frame} {ws : List Val} {k : BitVec 32} {bt : BlockType}
      {t e : List Instr} {code : List Admin}
      (h : R s f ws (.plain (.block bt (if k = 0 then e else t)) :: code)) :
      DivF P host R s f (ws ++ [.i32 k]) (.plain (.if_ bt t e) :: code)
  /-- The label's body diverges. -/
  | labelIn {s : Store H} {f : Frame} {vs : List Val} {n : Nat} {cont : List Instr}
      {inner code : List Admin} (h : R s f [] inner) :
      DivF P host R s f vs (.label n cont inner :: code)
  | labelNormal {s s₁ : Store H} {f f₁ : Frame} {vs us : List Val} {n : Nat}
      {cont : List Instr} {inner code : List Admin}
      (hin : Run P host s f [] inner s₁ f₁ (.normal us)) (h : R s₁ f₁ (vs ++ us) code) :
      DivF P host R s f vs (.label n cont inner :: code)
  | labelBr0 {s s₁ : Store H} {f f₁ : Frame} {vs us₁ us₂ : List Val} {n : Nat}
      {cont : List Instr} {inner code : List Admin}
      (hin : Run P host s f [] inner s₁ f₁ (.br 0 (us₁ ++ us₂))) (hn : us₂.length = n)
      (h : R s₁ f₁ vs (vals us₂ ++ expression cont ++ code)) :
      DivF P host R s f vs (.label n cont inner :: code)

/-- **Diverging region runs**: the greatest fixed point of `DivF`, as membership in some
`DivF`-closed relation. -/
def RunDiv (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame) (vs : List Val)
    (code : List Admin) : Prop :=
  ∃ R : Store H → Frame → List Val → List Admin → Prop,
    (∀ s f vs code, R s f vs code → DivF P host R s f vs code) ∧ R s f vs code

/-- **The atomic obligation**: the Core reduction of every non-control instruction, on any
values, store and frame, terminates. Termination includes ending in a trap. This is a named
hypothesis of completeness for divergence, not part of `RunDiv`: `RunDiv` itself never
appeals to Core divergence. -/
def AtomTerm (P : Profile) (host : HostSemantics H) : Prop :=
  ∀ (s : Store H) (f : Frame) (vs : List Val) (i : Instr),
    SingleThreaded.Det.famOf (.plain i) ≠ .control →
      Acc (fun a b => Step P host b a) (⟨s, f, vals vs ++ [.plain i]⟩ : Config H)

end Silmaril.Wasm.Cfg.Region
