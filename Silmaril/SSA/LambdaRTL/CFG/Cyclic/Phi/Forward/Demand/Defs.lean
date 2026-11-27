module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward.Defs

/-! # Inferring the forwarding table by edge demand

The table of the normalization is computed from the φ graph, its declared
exits and its declared inputs.

The demand of a block is the list of registers that the block needs from
its predecessors. It is read off the routes of the block, which list the
reads and definitions of each path through the block in execution order:
its φ destinations, the reads and definitions of its body, and at the end
the φ operands that the block supplies on that edge, or the payload of an
exit. A route that ends in a jump to a block also needs the demand of
that block. Walking a route backwards, a read adds its registers and a
definition removes its registers. So a register is demanded only where it
is read before any definition on the route, and the demand of a successor
stops at the definitions of the block.

Three kinds of register are then left out: the φ destinations of the
block, every register the block defines, and the declared inputs. The
declared inputs are the captures of the entry; they are never forwarded.

The demand of a block depends on the demands of its successors. It is
computed by as many rounds as there are blocks, starting from no demand,
which reaches every block of an acyclic graph. The table is checked like
any other table: nothing here assumes the graph is acyclic.
-/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward

universe v w

variable {V K : Type w} {F : Type v} [DecidableEq V] [DecidableEq K]

omit [DecidableEq K] in
/-- The registers that a list of accesses needs from before it: a read
adds its registers, and a definition removes its registers from what the
later accesses need. -/
def needs : List (GlobalSSA.Access V) → List V
  | [] => []
  | .read names :: rest => names ++ needs rest
  | .define names :: rest => (needs rest).filter fun register => !names.contains register

/-- The demand of one block, given the demand of every block it jumps to:
what its routes need, without the registers it defines and the declared
inputs. The routes are those of the graph with its exits collapsed, so
that the payload of an exit is a read. -/
def demandOf (routed : Graph V K F) (inputs : List V) (next : K → List V) (key : K)
    (source : Block V K F) : List V :=
  (((GlobalSSA.routes routed (some key)).flatMap fun route =>
      needs (route.accesses ++ [.read (route.target.elim [] next)])).filter fun register =>
    !(source.rows.map Row.dst ++ GlobalSSA.bodyDefinitions source.body ++ inputs).contains
      register).dedup

/-- One more round of demand, for every block. -/
def demandStep (graph routed : Graph V K F) (inputs : List V) (next : K → List V) (key : K) :
    List V :=
  (graph.blocks.lookup key).elim [] (demandOf routed inputs next key)

/-- The demand after a number of rounds, starting from no demand. -/
def demand (graph routed : Graph V K F) (inputs : List V) : Nat → K → List V
  | 0, _ => []
  | rounds + 1, key => demandStep graph routed inputs (demand graph routed inputs rounds) key

/-- The inferred table: every block receives its demand after as many
rounds as there are blocks. -/
def infer (graph : Graph V K F) (exits : List (Option K)) (inputs : List V) : Table V K :=
  let routed := OrderedExits.forScope graph exits
  graph.blocks.map fun (key, source) =>
    (key, demandOf routed inputs (demand graph routed inputs graph.blocks.length) key source)

/-- The arrival claims in which every block arrives with the declared
inputs only. -/
def inputArrivals (graph : Graph V K F) (inputs : List V) :
    GlobalSSA.Certificate (Name V K) K :=
  graph.blocks.map fun (key, _) => (key, inputs.map Sum.inl)

/-- Every block of the normalized graph is closed over the declared
inputs: the existing check accepts the normalized graph when every block
arrives with the declared inputs only. On each path through a block,
every read is then of an input, of a φ destination of the block, or of
an earlier definition of the block. -/
def closed (graph : Graph V K F) (table : Table V K) (exits : List (Option K))
    (inputs : List V) : Bool :=
  OrderedExits.check (forward graph table) exits (inputs.map Sum.inl) (inputArrivals graph inputs)

/-- The lowered and versioned entry of the normalized graph reads no
register at its initial version except the declared inputs. -/
def entryKept (graph : Graph V K F) (table : Table V K) (inputs : List V) : Bool :=
  (Versioning.compile (OrderedExits.lower (forward graph table))).entry.toRegion.fvList.all
    fun name => (inputs.map fun register => (some (Sum.inl register), 0)).contains name

/-- Open: a table under which every block is closed over the declared
inputs keeps the entry. It holds on the checked instances. -/
def Task.closedKeepsEntry (V K : Type w) (F : Type v) [DecidableEq V] [DecidableEq K] : Prop :=
  ∀ (graph : Graph V K F) (table : Table V K) (exits : List (Option K)) (inputs : List V),
    closed graph table exits inputs = true → entryKept graph table inputs = true

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward
