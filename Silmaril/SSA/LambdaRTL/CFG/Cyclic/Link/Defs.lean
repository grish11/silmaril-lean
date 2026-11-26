module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Institution.Refinement.Plugging.Thms
public import Mathlib.Logic.Equiv.Fin.Basic

/-! Finite packet interfaces for named cyclic CFGs. Private addresses name
existing blocks and public addresses name exit ports. An input port routes
its packet to a private block or directly to an exit. -/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link

open Silmaril.Elgot
open Comparison

abbrev Label (locals outputs : Nat) := Fin locals ⊕ Fin outputs

/-- One value of the common carrier crosses each port. A private block can
read only its incoming packet before defining local registers. -/
structure Graph (V F : Type) [DecidableEq V] (inputs outputs : Nat) where
  locals : Nat
  entry : Fin inputs → Label locals outputs
  block : Fin locals → Block V (Label locals outputs) F
  closed : ∀ i, (block i).body.toRegion.fv ⊆ {(block i).param}

variable {V F α : Type} [DecidableEq V] {a b c : Nat}

namespace Graph

/-- The machine's ordinary list table, with no public port installed as a block. -/
def table (graph : Graph V F a b) :
    List (Label graph.locals b × Block V (Label graph.locals b) F) :=
  (List.finRange graph.locals).map fun i => (.inl i, graph.block i)

/-- Start the ordinary CFG at one input port, reading the packet from the
designated register in the initial environment. -/
def toCFG [Inhabited V] (graph : Graph V F a b) (port : Fin a) :
    CFG V (Label graph.locals b) F :=
  ⟨.term (.br (graph.entry port) (.var default)), graph.table⟩

/-- Wires alone implement the identity. -/
def identity (a : Nat) : Graph V F a a where
  locals := 0
  entry := Sum.inr
  block := Fin.elim0
  closed i := Fin.elim0 i

/-- A private block executes on an environment seeded only by its argument.
A public address returns immediately. -/
def step (model : Model F Part α) (graph : Graph V F a b) :
    Label graph.locals b × α → Part ((Fin b × α) ⊕ (Label graph.locals b × α))
  | (.inl i, packet) =>
    let block := graph.block i
    Sum.inr <$> block.body.evalJump model (upd (fun _ => model.unit) block.param packet)
  | (.inr port, packet) => pure (.inl (port, packet))

/-- Observe a graph at one incoming port and packet. -/
noncomputable def denote (model : Model F Part α) (graph : Graph V F a b)
    (input : Fin a × α) : Part (Fin b × α) :=
  iter (graph.step model) (graph.entry input.1, input.2)

variable (left : Graph V F a b) (right : Graph V F b c)

abbrev linkedCount := left.locals + b + right.locals

/-- The first range holds left blocks and one handoff block per middle port. -/
def leftLabel (label : Label left.locals b) : Label (linkedCount left right) c :=
  .inl ((finSumFinEquiv label).castAdd right.locals)

/-- The second range holds right blocks and keeps right public exits public. -/
def rightLabel : Label right.locals c → Label (linkedCount left right) c :=
  Sum.map (Fin.natAdd (left.locals + b)) id

private theorem term_fv_relabel {K K' : Type} (rename : K → K') (term : Term V K F) :
    (term.relabel rename).toRegion.fv = term.toRegion.fv := by
  induction term <;> simp_all [Term.relabel, Term.toRegion, Region.fv]

private theorem body_fv_relabel {K K' : Type} (rename : K → K') (body : Body V K F) :
    (body.relabel rename).toRegion.fv = body.toRegion.fv := by
  induction body <;> simp_all [Body.relabel, Body.toRegion, Region.fv, term_fv_relabel]

variable [Inhabited V]

/-- The handoff forwards precisely the packet it receives. -/
def handoff (port : Fin b) : Block V (Label (linkedCount left right) c) F :=
  ⟨default, .term (.br (rightLabel left right (right.entry port)) (.var default))⟩

/-- Construct the linked block table by disjoint finite offsets. -/
def linkedBlock : Fin (linkedCount left right) → Block V (Label (linkedCount left right) c) F :=
  Fin.addCases
    (Fin.addCases (fun i => (left.block i).relabel (leftLabel left right)) (handoff left right))
    (fun i => (right.block i).relabel (rightLabel left right))

/-- Link two finite packet interfaces into one executable named table.
Both sides retain back edges and each former left exit becomes a handoff. -/
def link : Graph V F a c where
  locals := linkedCount left right
  entry input := leftLabel left right (left.entry input)
  block := linkedBlock left right
  closed i := by
    refine Fin.addCases (fun addr => ?_) (fun addr => ?_) i
    · refine Fin.addCases (fun index => ?_) (fun port => ?_) addr
      · simpa [linkedBlock, Block.relabel, body_fv_relabel] using left.closed index
      · simp [linkedBlock, handoff, Body.toRegion, Term.toRegion, Region.fv, Val.fv]
    · simpa [linkedBlock, Block.relabel, body_fv_relabel] using right.closed addr

end Graph

/-- Objects have finitely many ports and a fixed model profile. The carrier
of the packet at each port is `α`. -/
structure Interface (V F α : Type) where
  ports : Nat

/-- Equality of the observations of two executable graphs at every input
port and packet and in every common model. -/
def graphSetoid : Setoid (Graph V F a b) where
  r left right := ∀ (model : PairModel F Part α) (input : Fin a × α),
    left.denote model.val input = right.denote model.val input
  iseqv := ⟨fun _ _ _ => rfl, fun equal model input => (equal model input).symm,
    fun first second model input => (first model input).trans (second model input)⟩

/-- Arrows are represented by finite named CFG syntax. -/
abbrev Arrow (V F α : Type) [DecidableEq V] (inputs outputs : Nat) :=
  Quotient (graphSetoid (V := V) (F := F) (α := α) (a := inputs) (b := outputs))

noncomputable def observe (model : PairModel F Part α) (arrow : Arrow V F α a b)
    (input : Fin a × α) : Part (Fin b × α) :=
  Quotient.lift (s := graphSetoid (α := α)) (fun graph => graph.denote model.val input)
    (fun _ _ equivalent => equivalent model input) arrow

/-- Terminating-result inclusion at every input port and packet. -/
def Refines (lhs rhs : Arrow V F α a b) : Prop :=
  ∀ model input, observe model lhs input ≤ observe model rhs input

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link
