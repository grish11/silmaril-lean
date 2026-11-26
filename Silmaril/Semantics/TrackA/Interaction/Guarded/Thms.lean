module

public import Silmaril.Semantics.TrackA.Interaction.Guarded.Defs

public section

namespace Silmaril.Semantics.TrackA.Interaction.Guarded

/-- An erased visible step packages the source context with the request and
lands in the context determined by its typed reply. -/
theorem Forest.step_vis {World : Type*} {P : Protocol World} {B : Signature}
    {A I : Type*} (forest : Forest P B A I) {world : World}
    {state : forest.State world} {q : (P.effects world).Request}
    {next : (r : (P.effects world).Response q) → forest.State (P.advance world q r)}
    (layer : forest.unfold state = .vis q next) (reply : (P.effects world).Response q) :
    (forest.erase P).unfold.Step ⟨world, state⟩ (.exchange ⟨⟨world, q⟩, reply⟩)
      ⟨P.advance world q reply, next reply⟩ := by
  exact Coalgebra.Step.vis (c := (forest.erase P).unfold) (x := ⟨world, state⟩) (q := ⟨world, q⟩) (next := fun r => ⟨P.advance world q r, next r⟩)
    (congrArg (Node.erase P) layer) reply

end Silmaril.Semantics.TrackA.Interaction.Guarded
