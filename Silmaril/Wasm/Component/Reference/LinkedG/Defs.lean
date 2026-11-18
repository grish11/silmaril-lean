module

public import Silmaril.Wasm.Component.Reference.LinkedSessionIR.Defs
public import Silmaril.Wasm.Component.Reference.LinkedSessionDiv.Defs

/-!
# Linking with an abstract exporter, and chains of linked modules: definitions

**Scope.** The IR side (`Comp.denU`/`Comp.den` over `impSem P`) of `Linked2`, with the exporter
abstracted to an interface. The reference side (`toRef` on the reference machine) is not
covered by the theorems of this topic; `ExpSpec.ref` and `LinkedG.toRef` only record the
reference translation (see `Thms` for what the reference machine needs).

## The exporter interface `ExpSpec`

An exporter is

* `comp`: its IR component (`Comp ImpModule`), and `ref`, its reference component;
* a session specification: a state type `St`, the initial state `init` and a step relation
  `Step P s r s'` for one call (a round `r` at the untyped interface `sigU`: the export index
  and payload, and the IR answer, `none` for a trap). Steps thread the state across returned
  **and** trapped calls, as `Linked2.ExpRunT` does for `Simple`;
* `ExpSpec.Run`: sessions, steps one after another;
* a divergence specification `DivStep P s q`: from state `s`, the call `q` (at `sigU`) never
  answers. `LinkedGDiv` states its laws (`ExpSpec.AdeqD` on the IR side, R7 `RefData.Div` on the
  reference machine).

`ExpSpec.Adeq P e` (a `Prop`) is what the finite `Linked2` proofs use about the exporter on the
IR side: it imports nothing, its sessions from `init` are plays of `comp.denU (impSem P)`
(`fwd`), and conversely every play of complete rounds of typed calls (`ExpSpec.Typed`: an
export index in range and values of the export's parameter types) is a session from `init`
(`bwd`).

* `Simple.expSpec c I`: a simple component at its core instance `I`; the IR component is
  `(SimpleI.ofSimple c).toComp` (as in `Linked2.toComp`), the state A's Core store, a step a
  returned call (`RetAt`) or a trapped call (`TrapAt`) of one export (`Simple.ExpStep`), a
  diverging call one whose lowered Core activation runs forever host-free (`DivAt`).

## Linking an abstract exporter with an importer

`LinkedG := ⟨exp : ExpSpec, imp : SimpleI, wire⟩`, import `k` of `imp` answered by export
`wire[k]` of `exp`. `linkComp` (so `LinkedG.toComp`) is `Linked2.toComp` with the exporter's
IR component in place of `(SimpleI.ofSimple l.exp).toComp`; `LinkedG.ExpRun`, `SessRound`,
`SessSpec` and `sessMoves` are `Linked2.ExpRunT`, `Linked2.SessRound`, `Linked2.SessSpec` and
`Linked2.sessMoves` with the exporter's step in place of `RetAt`/`TrapAt`.
`Linked2.toG l Ie := ⟨Simple.expSpec l.exp Ie, l.imp, l.wire⟩` is the instance.

**Rounds that never answer** (`Linked2.RoundDiv` over the interface): `LinkedG.DivRound` (the
start of a round, well formed by `DivRound.Ok`), and `LinkedG.RoundDiv`: after the round's prefix,
whose import calls are an `ExpRun` of the exporter, (i) the importer diverges host-free
(`Linked2.DivB`), (ii) it calls out on arguments that lift and the wired export's call diverges by
the exporter's `DivStep` (`LinkedG.DivA`), or (iii) chatter (`LinkedG.Chatter`: infinitely many
import calls answered by the exporter's steps). `LinkedG.sessDivs`: a `SessSpec` session from the
importer's instance store and the exporter's initial state, then a round that never answers.

## A linked component as an exporter, and chains

`LinkedG.toExp g Ii`: the linked component at the importer's core instance `Ii` as an
exporter. Its IR component is `g.toComp`, its state the importer's Core store with the
exporter's state, a step one round of the linked session (`SessRound`, a play of `Ii` and
an `ExpRun` of the exporter), and a diverging call a `RoundDiv`. Its session relation is the
linked `SessSpec`.

`LinkedN := ⟨base : Simple, links : List (SimpleI × List Nat)⟩`: a chain in which each
importer imports from the component built so far (`LinkedN.toComp`, by `linkComp`).
`LinkedN.spec n Ib Is` is its specification as an exporter (`chainExp`, by `LinkedG.toExp`) at
the core instances `Ib` of the base and `Is` of the importers; `ChainOk` the hypotheses of each
link (the importer `Good`, its instance, `WireTy` against the component built so far).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (ScalarInstance)
open Silmaril.Wasm.Execution.Core (Store)

local notation "IVal" => Silmaril.Wasm.Component.Val

/-- A round at the untyped interface: a question (function index and payload) and its answer
(`none` for a trap). -/
abbrev URound : Type := Σ _ : sigU.Op, Option Payload

/-- The play answering the rounds one after another. -/
def uMoves : List URound → List (Silmaril.Games.Move sigU sigU)
  | [] => []
  | ⟨q, a⟩ :: L => .inr (.ask q) :: .inr (.ans q a) :: uMoves L

/-! ## The exporter interface -/

/-- **An exporter**: an IR component, its reference component, and a session specification
(state, initial state, one step per call, threading the state across returned and trapped
calls). -/
structure ExpSpec where
  /-- The IR component. -/
  comp : Comp ImpModule
  /-- The reference component. -/
  ref : Core3Component
  /-- The specification state. -/
  St : Type
  /-- The initial state. -/
  init : St
  /-- One call: from state `s`, the round `r`, to state `s'`. -/
  Step : Profile → St → URound → St → Prop
  /-- One call that never answers: from state `s`, the question `q` diverges. -/
  DivStep : Profile → St → sigU.Op → Prop

namespace ExpSpec

/-- **Sessions of an exporter**: steps one after another. -/
inductive Run (e : ExpSpec) (P : Profile) : e.St → List URound → e.St → Prop where
  | nil (s : e.St) : Run e P s [] s
  | cons {s s₁ s' : e.St} {r : URound} {L : List URound} :
      e.Step P s r s₁ → Run e P s₁ L s' → Run e P s (r :: L) s'

/-- A typed call: an export in range, on values of the export's parameter types. -/
def Typed (e : ExpSpec) (r : URound) : Prop :=
  ∃ (w : Fin e.comp.exports.length) (ws : List IVal), r.1 = (w.val, .vals ws) ∧
    ValTy.checkList e.comp.exports[w].ty.params ws = true

/-- **What linking uses of an exporter, on the IR side**: it imports nothing, its sessions from
the initial state are plays of its IR component, and every play of complete rounds of typed
calls is a session from the initial state. -/
structure Adeq (P : Profile) (e : ExpSpec) : Prop where
  imports : e.comp.imports = []
  fwd : ∀ (L : List URound) (s' : e.St), e.Run P e.init L s' →
    uMoves L ∈ e.comp.denU (impSem P)
  bwd : ∀ L : List URound, (∀ r ∈ L, e.Typed r) → uMoves L ∈ e.comp.denU (impSem P) →
    ∃ s', e.Run P e.init L s'

end ExpSpec

/-! ## A simple component as an exporter -/

/-- **One call of a simple component**, threading its Core store: a returned call (`RetAt`) or a
trapped call (`TrapAt`) of export `j`. -/
inductive Simple.ExpStep (c : Simple) (I : ScalarInstance) (P : Profile) :
    Store Nat → URound → Store Nat → Prop where
  | ret {s s' : Store Nat} {j : Nat} {vs ws : List IVal} (hj : j < c.exports.length) :
      RetAt P c I c.exports[j] vs s ws s' →
      Simple.ExpStep c I P s ⟨(j, .vals vs), some (.vals ws)⟩ s'
  | trap {s s' : Store Nat} {j : Nat} {vs : List IVal} (hj : j < c.exports.length) :
      TrapAt P c I c.exports[j] vs s s' → Simple.ExpStep c I P s ⟨(j, .vals vs), none⟩ s'

/-- **A simple component as an exporter**, at its core instance `I`. -/
abbrev Simple.expSpec (c : Simple) (I : ScalarInstance) : ExpSpec where
  comp := (SimpleI.ofSimple c).toComp
  ref := c.toRef
  St := Store Nat
  init := I.store
  Step P := Simple.ExpStep c I P
  DivStep P s q := ∃ (j : Fin c.exports.length) (vs : List IVal), q = (j.val, .vals vs) ∧
    DivAt P I c.exports[j] vs s

/-! ## Linking an abstract exporter with an importer -/

/-- **The IR composition of an exporter `A` and an importer `b`**, import `k` of `b` wired to
export `wire[k]` of `A` (`Linked2.toComp` with `A` for the exporter). -/
def linkComp (A : Comp ImpModule) (b : SimpleI) (wire : List Nat) : Comp ImpModule :=
  .mk [] [.inst A [], .inst b.toComp (wire.map fun w => ⟨[], .call w⟩)]
    (b.exports.mapIdx fun i x =>
      { name := x.name, ty := x.ty, impl := ⟨[], .call (A.exports.length + i)⟩ })

/-- **An abstract exporter linked with an importer**: import `k` of `imp` is answered by export
`wire[k]` of `exp`. -/
structure LinkedG where
  /-- The exporter. -/
  exp : ExpSpec
  /-- The importer. -/
  imp : SimpleI
  /-- For each import of `imp`, the index of the export of `exp` answering it. -/
  wire : List Nat

namespace LinkedG

/-- The IR composition. -/
def toComp (g : LinkedG) : Comp ImpModule := linkComp g.exp.comp g.imp g.wire

theorem exports_length_toComp (g : LinkedG) : g.toComp.exports.length = g.imp.exports.length := by
  simp [toComp, linkComp]

/-- The name of export `w` of the exporter (`""` out of range). -/
def expName (g : LinkedG) (w : Nat) : String :=
  ((g.exp.comp.exports[w]?).map (·.name)).getD ""

/-- The reference translation (`Linked2.toRef` with the exporter's reference component). -/
def toRef (g : LinkedG) : Core3Component :=
  [.component g.exp.ref, .component g.imp.toRef, .instance_ (.instantiate 0 [])] ++
    (g.wire.map fun w => .alias (.export_ 0 (g.expName w) .func)) ++
    [.instance_ (.instantiate 1 (g.imp.imports.mapIdx fun k p => (p.1, ⟨.func, k⟩)))] ++
    (g.imp.exports.map fun x => .alias (.export_ 1 x.name .func)) ++
    (g.imp.exports.mapIdx fun i x => .export_ { name := x.name } ⟨.func, g.wire.length + i⟩ none)

/-- **The wiring is well typed**: one wired export per import, of the import's type. -/
structure WireTy (g : LinkedG) : Prop where
  length : g.wire.length = g.imp.imports.length
  ty : ∀ (k w : Nat), g.wire[k]? = some w →
    ∃ x : Export, g.exp.comp.exports[w]? = some x ∧
      (g.imp.imports[k]?).map (fun p : String × FuncTy => p.2) = some x.ty

/-- **Import calls answered by the exporter's specification**: each call of import `k` is a
step of the exporter at the wired export `wire[k]`, threading the exporter's state. -/
inductive ExpRun (P : Profile) (g : LinkedG) :
    g.exp.St → List (Σ _ : (sigN g.imp.imports.length).Op, Option Payload) → g.exp.St → Prop
  | nil (s : g.exp.St) : ExpRun P g s [] s
  | step {s s₁ s' : g.exp.St} {k : Fin g.imp.imports.length} {p : Payload} {R : Option Payload}
      {ds : List (Σ _ : (sigN g.imp.imports.length).Op, Option Payload)}
      (w : Fin g.exp.comp.exports.length) :
      g.wire[k.val]? = some w.val → g.exp.Step P s ⟨(w.val, p), R⟩ s₁ → ExpRun P g s₁ ds s' →
      ExpRun P g s (⟨(k, p), R⟩ :: ds) s'

/-- **One export call of a linked session, on the importer's side** (`Linked2.SessRound`). -/
structure SessRound (g : LinkedG) (Ii : ScalarInstance) where
  /-- The export of the importer (and of the linked component). -/
  j : Fin g.imp.exports.length
  /-- The IR arguments. -/
  vs : List IVal
  /-- The core question of the importer's instance. -/
  f : Ii.F.Op
  /-- The core import calls, with their answers. -/
  cs : List (Σ e : Ii.E.Op, Ii.E.Ar e)
  /-- The core answer. -/
  w : Ii.F.Ar f
  /-- The component import calls of each core import call. -/
  dss : List (List (Σ _ : (sigN g.imp.imports.length).Op, Option Payload))

namespace SessRound

variable {g : LinkedG} {Ii : ScalarInstance} (d : SessRound g Ii)

/-- The round is well formed (`Linked2.SessRound.Ok`). -/
def Ok : Prop :=
  ∃ xs : List Flat, checkLower g.imp.exports[d.j].ty.params d.vs = some xs ∧
    d.f.1.val = g.imp.exports[d.j].core ∧ d.f.2.1 = xs.map Silmaril.Wasm.SingleThreaded.ofFlat ∧
    List.Forall₂ (ImpRel g.imp Ii) d.cs d.dss

/-- The play of the importer's core instance. -/
def instMoves : List (Silmaril.Games.Move Ii.E Ii.F) :=
  .inr (.ask d.f) :: callMoves d.cs ++ [.inr (.ans d.f d.w)]

/-- The lifted answer of the round. -/
def ans : Option Payload :=
  (answerPayload d.w).bind (Adapter.up (.lift g.imp.exports[d.j].ty))

/-- The round of the linked component at the untyped interface. -/
def toU : URound := ⟨(d.j.val, .vals d.vs), d.ans⟩

end SessRound

/-- **The specification of a linked session** (`Linked2.SessSpec`): from the importer's store
`u` and the exporter's state `π`, each call is a round of the importer's core instance whose
component import calls are an `ExpRun` of the exporter, and whose lifted answer is the
outcome. -/
inductive SessSpec (P : Profile) (g : LinkedG) (Ii : ScalarInstance) :
    Store Nat → g.exp.St → List (Fin g.imp.exports.length × List IVal) →
    List (Option (List IVal)) → Store Nat → g.exp.St → Prop
  | nil (u : Store Nat) (π : g.exp.St) : SessSpec P g Ii u π [] [] u π
  | round {u u₁ u' : Store Nat} {π π₁ π' : g.exp.St}
      {cs : List (Fin g.imp.exports.length × List IVal)} {outs : List (Option (List IVal))}
      {o : Option (List IVal)} (d : SessRound g Ii) :
      d.Ok → Ii.Path P (.idle u) d.instMoves (.idle u₁) → ExpRun P g π d.dss.flatten π₁ →
      d.ans = o.map .vals → SessSpec P g Ii u₁ π₁ cs outs u' π' →
      SessSpec P g Ii u π ((d.j, d.vs) :: cs) (o :: outs) u' π'

/-- **The IR play of a linked session** (`Linked2.sessMoves`). -/
def sessMoves (g : LinkedG) :
    List (Fin g.imp.exports.length × List IVal) → List (Option (List IVal)) →
    List (Silmaril.Games.Move g.toComp.imports.sig (sigN g.toComp.exports.length))
  | (j, vs) :: cs, o :: os =>
    .inr (.ask (⟨j, by simp [exports_length_toComp]⟩, .vals vs)) ::
      .inr (.ans (m := (⟨j, by simp [exports_length_toComp]⟩, .vals vs)) (o.map .vals)) ::
      sessMoves g cs os
  | _, _ => []

/-! ### Rounds that never answer -/

/-- **The start of a round that does not answer** (`Linked2.DivRound`): export `j` of the
importer on `vs`, the core question `f` of the importer's instance, the core import calls `cs`
made so far (with their answers), and the component import calls `dss` they correspond to. -/
structure DivRound (g : LinkedG) (Ii : ScalarInstance) where
  /-- The export of the importer (and of the linked component). -/
  j : Fin g.imp.exports.length
  /-- The IR arguments. -/
  vs : List IVal
  /-- The core question of the importer's instance. -/
  f : Ii.F.Op
  /-- The core import calls so far, with their answers. -/
  cs : List (Σ e : Ii.E.Op, Ii.E.Ar e)
  /-- The component import calls of each core import call. -/
  dss : List (List (Σ _ : (sigN g.imp.imports.length).Op, Option Payload))

namespace DivRound

variable {g : LinkedG} {Ii : ScalarInstance} (d : DivRound g Ii)

/-- The round is well formed, as `SessRound.Ok`. -/
def Ok : Prop :=
  ∃ xs : List Flat, checkLower g.imp.exports[d.j].ty.params d.vs = some xs ∧
    d.f.1.val = g.imp.exports[d.j].core ∧ d.f.2.1 = xs.map Silmaril.Wasm.SingleThreaded.ofFlat ∧
    List.Forall₂ (ImpRel g.imp Ii) d.cs d.dss

/-- The play of the importer's core instance so far: the question and the import calls. -/
def instMoves : List (Silmaril.Games.Move Ii.E Ii.F) :=
  .inr (.ask d.f) :: callMoves d.cs

end DivRound

/-- **(ii) The exporter's served call diverges** (`Linked2.DivA` with the exporter's `DivStep`):
from the running export call `f` at `(s, t)`, the importer calls out (core import `e`), the
arguments lift at the import's type to `ws`, and the call of the wired export `w` on `ws`
diverges from the exporter's state `π`. -/
def DivA (P : Profile) (g : LinkedG) (Ii : ScalarInstance) (f : Ii.F.Op) (s : Store Nat)
    (t : Silmaril.Wasm.SingleThreaded.Thread) (π : g.exp.St) : Prop :=
  ∃ (e : Ii.E.Op) (s' : Store Nat) (t' : Silmaril.Wasm.SingleThreaded.Thread) (nm : String)
    (ft : FuncTy) (ws : List IVal) (w : Fin g.exp.comp.exports.length),
    Ii.Path P (.running f s t) [.inl (.ask e)] (.waiting f s' t' e) ∧
    g.imp.imports[e.1.val]? = some (nm, ft) ∧
    liftArgs ft.params (e.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat?) = some ws ∧
    g.wire[e.1.val]? = some w.val ∧ g.exp.DivStep P π (w.val, .vals ws)

/-- **(iii) Chatter** (`Linked2.Chatter`): from the running export call `f` at `(s, t)`, the
importer makes infinitely many core import calls `c 0, c 1, …`, each related to component import
calls `ds k` (`ImpRel`) answered by the exporter's specification, from its state `π` on
(`ExpRun`). -/
def Chatter (P : Profile) (g : LinkedG) (Ii : ScalarInstance) (f : Ii.F.Op) (s : Store Nat)
    (t : Silmaril.Wasm.SingleThreaded.Thread) (π : g.exp.St) : Prop :=
  ∃ (q : ℕ → Ii.HState) (c : ℕ → Σ e : Ii.E.Op, Ii.E.Ar e)
    (ds : ℕ → List (Σ _ : (sigN g.imp.imports.length).Op, Option Payload))
    (st : ℕ → g.exp.St),
    q 0 = .running f s t ∧ st 0 = π ∧
    ∀ k, Ii.Path P (q k) (callMoves [c k]) (q (k + 1)) ∧ ImpRel g.imp Ii (c k) (ds k) ∧
      ExpRun P g (st k) (ds k) (st (k + 1))

/-- **A round that never answers** (`Linked2.RoundDiv`): from the importer's store `u` and the
exporter's state `π`, the call of export `j` on `vs` starts a well-formed round whose import calls
so far are answered by the exporter, and then diverges: (i) the importer diverges host-free
(`Linked2.DivB`), (ii) the exporter's served call diverges (`DivA`), or (iii) chatter. -/
def RoundDiv (P : Profile) (g : LinkedG) (Ii : ScalarInstance) (u : Store Nat) (π : g.exp.St)
    (j : Fin g.imp.exports.length) (vs : List IVal) : Prop :=
  ∃ (d : DivRound g Ii) (s : Store Nat) (t : Silmaril.Wasm.SingleThreaded.Thread)
    (π₁ : g.exp.St),
    d.j = j ∧ d.vs = vs ∧ d.Ok ∧ Ii.Path P (.idle u) d.instMoves (.running d.f s t) ∧
    ExpRun P g π d.dss.flatten π₁ ∧
    (Linked2.DivB P s t ∨ DivA P g Ii d.f s t π₁ ∨ Chatter P g Ii d.f s t π₁)

/-- **The diverging session calls of the specification** (`Linked2.sessDivs`): the outcomes
`outs` of a specification session of `calls` from the importer's store `Ii.store` and the
exporter's initial state, after which the call of export `j` on `vs` diverges. -/
def sessDivs (P : Profile) (g : LinkedG) (Ii : ScalarInstance)
    (calls : List (Fin g.imp.exports.length × List IVal)) (j : Fin g.imp.exports.length)
    (vs : List IVal) : Set (List (Option (List IVal))) :=
  {outs | ∃ (u : Store Nat) (π : g.exp.St), SessSpec P g Ii Ii.store g.exp.init calls outs u π ∧
    RoundDiv P g Ii u π j vs}

/-- **A linked component as an exporter**, at the importer's core instance `Ii`: a step is one
round of the linked session. -/
abbrev toExp (g : LinkedG) (Ii : ScalarInstance) : ExpSpec where
  comp := g.toComp
  ref := g.toRef
  St := Store Nat × g.exp.St
  init := (Ii.store, g.exp.init)
  Step P s r s' := ∃ d : SessRound g Ii, d.Ok ∧ Ii.Path P (.idle s.1) d.instMoves (.idle s'.1) ∧
    ExpRun P g s.2 d.dss.flatten s'.2 ∧ r = d.toU
  DivStep P s q := ∃ (j : Fin g.imp.exports.length) (vs : List IVal), q = (j.val, .vals vs) ∧
    RoundDiv P g Ii s.1 s.2 j vs

end LinkedG

/-- **`Linked2` as an instance**: the exporter as `Simple.expSpec` at its core instance `Ie`. -/
abbrev Linked2.toG (l : Linked2) (Ie : ScalarInstance) : LinkedG :=
  ⟨Simple.expSpec l.exp Ie, l.imp, l.wire⟩

/-! ## Chains -/

/-- **A chain of linked modules**: the base exporter, then importers, each importing from the
component built so far (with its wiring). -/
structure LinkedN where
  /-- The first exporter. -/
  base : Simple
  /-- The importers, in order, with their wiring. -/
  links : List (SimpleI × List Nat)

/-- The IR component of a chain built on `A`. -/
def chainComp (A : Comp ImpModule) : List (SimpleI × List Nat) → Comp ImpModule
  | [] => A
  | (b, w) :: bs => chainComp (linkComp A b w) bs

/-- The specification of a chain built on the exporter `e`, at the importers' core instances. -/
def chainExp (e : ExpSpec) : List (SimpleI × List Nat) → List ScalarInstance → ExpSpec
  | (b, w) :: bs, I :: Is => chainExp (LinkedG.toExp ⟨e, b, w⟩ I) bs Is
  | _, _ => e

/-- **The hypotheses of the links of a chain** built on `e`: each importer is `Good`, `I` is an
instance of its core module, and its wiring is well typed against the component built so far;
one instance per importer. -/
def ChainOk : ExpSpec → List (SimpleI × List Nat) → List ScalarInstance → Prop
  | _, [], [] => True
  | e, (b, w) :: bs, I :: Is =>
    b.Good ∧ b.mod.IsInst I ∧ (LinkedG.mk e b w).WireTy ∧
      ChainOk (LinkedG.toExp ⟨e, b, w⟩ I) bs Is
  | _, _, _ => False

namespace LinkedN

/-- The IR component of the chain. -/
def toComp (n : LinkedN) : Comp ImpModule :=
  chainComp (SimpleI.ofSimple n.base).toComp n.links

/-- The specification of the chain as an exporter, at the core instance `Ib` of the base and
`Is` of the importers. -/
def spec (n : LinkedN) (Ib : ScalarInstance) (Is : List ScalarInstance) : ExpSpec :=
  chainExp (Simple.expSpec n.base Ib) n.links Is

end LinkedN

end Silmaril.Wasm.Component.Reference
