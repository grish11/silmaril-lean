module

public import Silmaril.SSA.RVSDG.NestedTheta.Equality.Thms

/-! # Check supplied maps between numbered nested graphs -/

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Isomorphism

/-- Proposed maps on row numbers for a single scope. Only in-range rows
are read, and both round trips are checked on the finite tables. -/
structure VertexMap where
  forward : Nat → Nat
  backward : Nat → Nat

/-- A child path lists (actual vertex, arm or body position) from the
root. Boundary ports and arm positions are fixed. -/
abbrev Mapping := List (Nat × Nat) → VertexMap

def VertexMap.check (m : VertexMap) (n k : Nat) : Option (Fin n ≃ Fin k) :=
  if hf : ∀ i : Fin n, m.forward i < k then
    if hb : ∀ j : Fin k, m.backward j < n then
      let f (i : Fin n) : Fin k := ⟨m.forward i, hf i⟩
      let b (j : Fin k) : Fin n := ⟨m.backward j, hb j⟩
      if left : ∀ i, b (f i) = i then
        if right : ∀ j, f (b j) = j then some ⟨f, b, left, right⟩ else none
      else none
    else none
  else none

universe u v
variable {V S : Type u} {Op : Dialect.{u,v} V S}

variable [DecidableEq (PortType V S)]
variable (code : Equality.OpcodeCode Op) [DecidableEq code.Key]

private def decideLabel (x y : NodeLabel Op) : Decidable (x = y) := by
  obtain ⟨ins, outs, kind⟩ := x
  obtain ⟨ins', outs', kind'⟩ := y
  refine if hi : ins = ins' then ?_ else .isFalse (fun h => hi (congrArg NodeLabel.ins h))
  subst ins'
  refine if ho : outs = outs' then ?_ else .isFalse (fun h => ho (congrArg NodeLabel.outs h))
  subst outs'
  exact decidable_of_iff (Equality.kindCode code kind = Equality.kindCode code kind')
    ⟨fun h => congrArg (NodeLabel.mk ins outs) (Equality.kind_injective code kind kind' h),
      fun h => by cases h; rfl⟩

variable (mapping : Mapping)

private def checkScope :
    {argsL argsR outsL outsR : Ports (PortType V S)} →
    {pastL sigsL sigsR : List (Ports (PortType V S))} →
    (path : List (Nat × Nat)) → (left : Graph Op argsL pastL sigsL outsL) →
    (right : Graph Op argsR [] sigsR outsR) → (closed : pastL = []) →
    Option (PLift (Graph.Isomorphic Op (closed ▸ left) right))
  | argsL, argsR, outsL, outsR, _, sigsL, sigsR, path, .region nodes children results, right, rfl => do
    let ids ← (mapping path).check sigsL.length sigsR.length
    if entry : argsL = argsR then
      if exit : outsL = outsR then
        letI (i : Fin sigsL.length) : Decidable ((nodes i).label = (right.nodes (ids i)).label) :=
          decideLabel code _ _
        if labels : ∀ i, (nodes i).label = (right.nodes (ids i)).label then
          let rename := Address.rename (renameVertex ids)
          if inputs : ∀ i, (nodes i).inputs.addresses.map rename = (right.nodes (ids i)).inputs.addresses then
            if outputs : results.addresses.map rename = right.results.addresses then
              let child (i : Fin sigsL.length) (j : Fin (nodes i).kind.arity) :=
                checkScope (path ++ [(i.val, j.val)]) (children i j)
                  (right.children (ids i) (Fin.cast (congrArg NodeLabel.arity (labels i)) j)) rfl
              if complete : ∀ i j, (child i j).isSome then
                some ⟨.intro entry exit ids labels inputs outputs (fun i j => ((child i j).get (complete i j)).down)⟩
              else none
            else none
          else none
        else none
      else none
    else none

termination_by structural _ _ _ _ _ _ _ _ left _ _ => left

/-- Check the maps against the actual typed tables, preserving every
ordered input, result and child port. A successful check supplies the
existing isomorphism certificate for these two graphs. -/
def check {args outs : Ports (PortType V S)} {sigsL sigsR : List (Ports (PortType V S))}
    (left : Graph Op args [] sigsL outs) (right : Graph Op args [] sigsR outs) :
    Option (PLift (Graph.Isomorphic Op left right)) :=
  checkScope code mapping [] left right rfl

end Silmaril.SSA.RVSDG.NestedTheta.Isomorphism
