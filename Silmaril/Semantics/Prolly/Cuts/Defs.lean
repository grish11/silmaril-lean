module

public import Silmaril.Semantics.Prolly.Defs

@[expose] public section

namespace Silmaril.Semantics.Prolly

variable {Item Key Payload : Type}

/-- No item ends a chunk, starting after `count` already consumed items. -/
def NoCuts (cut : Nat → Item → Bool) : Nat → List Item → Prop
  | _, [] => True
  | count, head :: tail => cut (count + 1) head = false ∧ NoCuts cut (count + 1) tail

/-- A partition into nonempty chunks, each cut at the first eligible end. Only
the final chunk may end with no eligible cut (exhaustion of the input). -/
inductive CutPartition (cut : Nat → Item → Bool) : List (List Item) → Prop where
  | nil : CutPartition cut []
  | final {group : List Item} : group ≠ [] → NoCuts cut 0 group → CutPartition cut [group]
  | boundary {initial : List Item} {last : Item} {rest : List (List Item)} :
      NoCuts cut 0 initial → cut (initial.length + 1) last = true → CutPartition cut rest →
      CutPartition cut ((initial ++ [last]) :: rest)

/-- Declarative bottom-up construction: each over-width level takes its unique
partition; the first level that fits is the root. This does not read CAS. -/
inductive CanonicalGrowth (policy : Policy Key) :
    (level : Nat) → Node Key Payload level → Tree Key Payload → Prop where
  | fits {level : Nat} {node : Node Key Payload level} :
      node.length ≤ policy.width → CanonicalGrowth policy level node ⟨level, node⟩
  | step {level : Nat} {node : Node Key Payload level} {groups : List (Node Key Payload level)}
      {tree : Tree Key Payload} :
      policy.width < node.length → groups.flatten = node →
      CutPartition (fun count pair => policy.cut level count pair.1) groups →
      CanonicalGrowth policy (level + 1) (lift groups) tree → CanonicalGrowth policy level node tree

end Silmaril.Semantics.Prolly
