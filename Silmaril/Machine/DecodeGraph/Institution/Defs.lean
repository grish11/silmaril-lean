module

public import Silmaril.Machine.DecodeGraph.Defs

/-! # Exact-success decoder institution

Fix the query context and byte/span carriers. Signatures are instruction types,
with functions as signature arrows. Models are success graphs (taken as
discrete model categories). An atom asserts one exact graph entry.
-/

@[expose] public section

namespace Silmaril.Machine.DecodeGraph.Institution

abbrev Atom (Context Instr : Type*) := (Context × Bytes) × (Instr × Nat)

variable {Context Source Target : Type*}

/-- Change only the named instruction, preserving the context, bytes and span. -/
def translate (f : Source → Target) (atom : Atom Context Source) : Atom Context Target :=
  (atom.1, (f atom.2.1, atom.2.2))

/-- Inverse image, not the forward transport of successes along `f`. -/
def reduct (f : Source → Target) (model : Graph Context Target) : Graph Context Source :=
  Set.preimage (translate f) model

def Satisfies (model : Graph Context Source) (atom : Atom Context Source) : Prop := atom ∈ model

end Silmaril.Machine.DecodeGraph.Institution
