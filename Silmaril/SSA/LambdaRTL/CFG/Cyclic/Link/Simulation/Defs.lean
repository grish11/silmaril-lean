module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Institution.Thms
import Mathlib.Data.Finset.Card

/-! A syntactic forward simulation of named packet CFGs. A private address
may be mapped to a private address or a public port. Copying matches the
whole labelled body after renaming. Skipping is allowed for a jump that
forwards its parameter unchanged and stays at the same mapped address,
including after a sequence of typed register copies. -/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link

variable {V F : Type} [DecidableEq V] {a b n : Nat}

/-- A graph made entirely of direct port-to-port wires. -/
def Graph.wiring (wire : Fin a → Fin b) : Graph V F a b where
  locals := 0
  entry := Sum.inr ∘ wire
  block := Fin.elim0
  closed i := Fin.elim0 i

namespace PacketCopy

variable {K : Type}

/-- The read context contains the registers typed as holding the incoming
packet. A copy types its destination only after its source has been read. -/
inductive Forwards : Finset V → Body V K F → K → Prop
  | jump {available : Finset V} {src : V} {target : K} (read : src ∈ available) :
      Forwards available (.term (.br target (.var src))) target
  | copy {available : Finset V} {src dst : V} {rest : Body V K F} {target : K}
      (read : src ∈ available) (next : Forwards (insert dst available) rest target) :
      Forwards available (.let1 dst (.val (.var src)) rest) target

/-- Check reads in program order and return the only possible jump target. -/
def target? (available : Finset V) : Body V K F → Option K
  | .let1 dst (.val (.var src)) rest =>
      if src ∈ available then target? (insert dst available) rest else none
  | .term (.br target (.var src)) =>
      if src ∈ available then some target else none
  | _ => none

end PacketCopy

namespace CopyChain

variable (graph : Graph V F a b)

/-- The unique syntactically checked successor of a private block. -/
def next? (index : Fin graph.locals) : Option (Label graph.locals b) :=
  PacketCopy.target? {(graph.block index).param} (graph.block index).body

/-- A path of typed forwarders, recording the private blocks it visits. -/
inductive Path : Label graph.locals b → List (Fin graph.locals) → Fin b → Prop
  | exit (port : Fin b) : Path (.inr port) [] port
  | step {index : Fin graph.locals} {next : Label graph.locals b}
      {rest : List (Fin graph.locals)} {port : Fin b}
      (forwarded : PacketCopy.Forwards {(graph.block index).param} (graph.block index).body next)
      (tail : Path next rest port) :
      Path (.inl index) (index :: rest) port

/-- Follow at most `fuel` private jumps. A public label consumes no fuel. -/
def terminalWithin? : Nat → Label graph.locals b → Option (Fin b)
  | _, .inr port => some port
  | 0, .inl _ => none
  | fuel + 1, .inl index => (next? graph index).bind (terminalWithin? fuel)

/-- Search for the terminal port using one unit of fuel per private block. -/
def terminal? (start : Label graph.locals b) : Option (Fin b) :=
  terminalWithin? graph graph.locals start

/-- The label-map certificate covers the entire private table, including
blocks that no input can reach. Each must lead to a public port. -/
def Total : Prop := ∀ index, (terminal? graph (.inl index)).isSome

/-- The port assigned to a private address by the traversal. -/
def terminalPort (total : Total graph) (index : Fin graph.locals) : Fin b :=
  (terminal? graph (.inl index)).get (total index)

/-- Check totality on private labels and agreement with the wire at inputs. -/
def check (wire : Fin a → Fin b) : Bool :=
  (List.finRange graph.locals).all (fun index => (terminal? graph (.inl index)).isSome) &&
  (List.finRange a).all (fun input => decide (terminal? graph (graph.entry input) = some (wire input)))

/-- Reachability using only typed copy-forwarding edges. -/
inductive Reaches : Label graph.locals b → Label graph.locals b → Prop
  | here (label : Label graph.locals b) : Reaches label label
  | step {index : Fin graph.locals} {next finish : Label graph.locals b}
      (forwarded : PacketCopy.Forwards {(graph.block index).param} (graph.block index).body next)
      (tail : Reaches next finish) : Reaches (.inl index) finish

/-- A private block reached from any input must be a typed forwarder.
There is no restriction on blocks outside these paths. -/
def EntryTyped : Prop :=
  ∀ input index, Reaches graph (graph.entry input) (.inl index) →
    ∃ next, PacketCopy.Forwards {(graph.block index).param} (graph.block index).body next

/-- A nonempty walk of typed forwarding edges back to this block. -/
def LoopsAt (index : Fin graph.locals) : Prop :=
  ∃ next, PacketCopy.Forwards {(graph.block index).param} (graph.block index).body next ∧
    Reaches graph next (.inl index)

inductive Outcome (locals outputs : Nat) where
  | returns (port : Fin outputs)
  | cycle (repeated : Fin locals)
  | unsupported (index : Fin locals)
  deriving DecidableEq

/-- Each recursive call consumes one unvisited private label. A private
label outside `remaining` is a repeat when started with the full table. -/
def inspect (remaining : Finset (Fin graph.locals)) (start : Label graph.locals b) :
    Outcome graph.locals b :=
  match start with
  | .inr port => .returns port
  | .inl index =>
    if _fresh : index ∈ remaining then
      match next? graph index with
      | none => .unsupported index
      | some next => inspect (remaining.erase index) next
    else .cycle index
termination_by remaining.card
decreasing_by exact Finset.card_erase_lt_of_mem _fresh

/-- Inspect only the path from the chosen input. -/
def entryOutcome (input : Fin a) : Outcome graph.locals b :=
  inspect graph Finset.univ (graph.entry input)

/-- A cycle contributes no terminating result. Unsupported reachable
syntax makes the comparison inconclusive. -/
def Outcome.agrees? (expected : Fin b) : Outcome n b → Option Bool
  | .returns port => some (decide (port = expected))
  | .cycle _ => some true
  | .unsupported _ => none

/-- Decide terminating-result inclusion against a wire on the entry-typed
fragment. `none` reports a reachable unsupported block at some input. -/
def refinement? (wire : Fin a → Fin b) : Option Bool :=
  let results := (List.finRange a).map fun input => (entryOutcome graph input).agrees? (wire input)
  if results.all Option.isSome then some (results.all (· == some true)) else none

end CopyChain

/-- The local syntactic simulation rules. -/
inductive BlockMatch (right : Graph V F a b) (route : Label n b → Label right.locals b)
    (source : Block V (Label n b) F) (image : Label right.locals b) : Prop
  | copy (target : Fin right.locals) (address : image = .inl target)
      (body : source.relabel route = right.block target) : BlockMatch right route source image
  | forward (target : Label n b)
      (body : source.body = .term (.br target (.var source.param)))
      (address : image = route target) : BlockMatch right route source image
  | forwardCopies (target : Label n b)
      (copies : PacketCopy.Forwards {source.param} source.body target)
      (address : image = route target) : BlockMatch right route source image

/-- The certificate maps private labels and leaves public exits unchanged. -/
structure Simulation (left right : Graph V F a b) where
  address : Fin left.locals → Label right.locals b
  entry : ∀ port, Sum.elim address Sum.inr (left.entry port) = right.entry port
  block : ∀ i, BlockMatch right (Sum.elim address Sum.inr) (left.block i) (address i)

namespace Simulation

variable {left right : Graph V F a b}

def route (sim : Simulation left right) : Label left.locals b → Label right.locals b :=
  Sum.elim sim.address Sum.inr

/-- Combine the address maps in the two private ranges and match each middle
port's handoff to the same port's handoff in the target. -/
def linkedAddress {c : Nat} {next next' : Graph V F b c}
    (first : Simulation left right) (second : Simulation next next') :
    Fin (left.linkedCount next) → Label (right.linkedCount next') c :=
  Fin.addCases
    (Fin.addCases (fun index => right.leftLabel next' (first.address index))
      (fun port => right.leftLabel next' (.inr port)))
    (fun index => right.rightLabel next' (second.address index))

/-- Check the local rules for a proposed map of private addresses. -/
def checkBlock [DecidableEq F] (right : Graph V F a b) (route : Label n b → Label right.locals b)
    (source : Block V (Label n b) F) (image : Label right.locals b) : Bool :=
  let copy := match image with
    | .inl target => decide (source.relabel route = right.block target)
    | .inr _ => false
  copy || match PacketCopy.target? {source.param} source.body with
    | some target => decide (image = route target)
    | none => false

/-- Check a finite certificate over all input ports and private blocks. -/
def check [DecidableEq F] (left right : Graph V F a b)
    (address : Fin left.locals → Label right.locals b) : Bool :=
  let route := Sum.elim address Sum.inr
  (List.finRange a).all (fun port => decide (route (left.entry port) = right.entry port)) &&
    (List.finRange left.locals).all (fun index => checkBlock right route (left.block index) (address index))

end Simulation

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link
