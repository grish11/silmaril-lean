module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Version.Defs
public import Silmaril.SSA.LambdaRTL.Nameless.Defs
public import Silmaril.SSA.LambdaRTL.RoundTrip.Defs

/-! Retain the compiled packets and their decoders when reading a versioned
cyclic table back as a mutable graph over the original register type. -/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic

universe v w

variable {V W K : Type w} {F : Type v}

namespace RoundTrip

/-- Each labelled body receives all its free inputs in its incoming packet.
The entry may read directly from its own initial environment. -/
def PacketClosed [DecidableEq V] (graph : CFG V K F) : Prop :=
  ∀ item ∈ graph.blocks, item.2.body.toRegion.fv ⊆ {item.2.param}

/-- Rename register uses and case binders in a terminator. -/
def renameTerm (rename : V → W) : Term V K F → Term W K F
  | .br label value => .br label (value.rename rename)
  | .case op x left y right =>
      .case (op.rename rename) (rename x) (renameTerm rename left) (rename y) (renameTerm rename right)

/-- Rename register reads and writes in a body, preserving instruction order. -/
def renameBody (rename : V → W) : Body V K F → Body W K F
  | .let1 x op rest => .let1 (rename x) (op.rename rename) (renameBody rename rest)
  | .let2 x y op rest => .let2 (rename x) (rename y) (op.rename rename) (renameBody rename rest)
  | .term term => .term (renameTerm rename term)

/-- Rename register reads, writes and parameters, keeping the table order and labels. -/
def renameGraph (rename : V → W) (graph : CFG V K F) : CFG W K F :=
  ⟨renameBody rename graph.entry, graph.blocks.map fun (label, block) =>
    (label, ⟨rename block.param, renameBody rename block.body⟩)⟩

/-- The support includes assignments and even unused block parameters, since
a hit writes its parameter before running the body. -/
noncomputable def support [DecidableEq V] (graph : CFG V K F) : Finset V :=
  graph.entry.toRegion.vars ∪
    (graph.blocks.flatMap fun (_, block) => block.param :: block.body.toRegion.vars.toList).toFinset

/-- Read a lexical table as mutable RTL, retaining the packet convention
and fixing version-zero names. All other used names are fresh on the support. -/
noncomputable def deversionGraph [DecidableEq V] [Infinite V]
    (graph : CFG (V × Nat) K F) : CFG V K F :=
  renameGraph (LambdaRTL.RoundTrip.deversion (support graph)) graph

end RoundTrip

/-- Version a cyclic graph and assign names in the original register type to
all the versions in its support. Internal transfers keep the packet as a
single parameter until the destination's existing decoder reads it. -/
noncomputable def Versioning.roundTrip [DecidableEq V] [DecidableEq K] [Infinite V]
    (graph : CFG V K F) : CFG V K F :=
  RoundTrip.deversionGraph (compile graph)

end Silmaril.SSA.LambdaRTL.CFG.Cyclic
