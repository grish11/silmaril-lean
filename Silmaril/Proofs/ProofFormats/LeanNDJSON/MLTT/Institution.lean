module

public import Silmaril.ProofFormats.LeanNDJSON.MLTT.Defs
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Institution.Defs

public section

namespace Silmaril.Proofs.ProofFormats.LeanNDJSON.MLTT

open Silmaril.ProofFormats.LeanNDJSON.MLTT
open Silmaril.Logic.TypeTheory.ExtensionalMLTT

theorem derives_iff_mltt {Name : Type} {S : Signature Name} (H : Set (Sentence S))
    (s : Sentence S) :
    Derives H s ↔ Institution.logic.{0}.Derives (CategoryTheory.Discrete.mk ())
      ((fun q : Sentence S => ULift.up q.judgment) '' H) (ULift.up s.judgment) := by
  change Derives H s ↔ s.judgment.Γ.JEqH
    (ULift.down '' ((fun q : Sentence S => ULift.up.{1} q.judgment) '' H))
    s.judgment.A s.judgment.a s.judgment.b
  rw [Set.image_image]
  rfl

end Silmaril.Proofs.ProofFormats.LeanNDJSON.MLTT
