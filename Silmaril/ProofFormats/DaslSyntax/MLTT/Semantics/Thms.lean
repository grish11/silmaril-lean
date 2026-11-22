module

public import Silmaril.ProofFormats.DaslSyntax.MLTT.Semantics.Defs
public import Silmaril.ProofFormats.DaslSyntax.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Soundness

public section

namespace Silmaril.ProofFormats.DaslSyntax.MLTT

open Silmaril.Formats.Dasl
open Silmaril.Logic.TypeTheory.ExtensionalMLTT

universe u

theorem inhabits_sound (model : SetHierarchy.{u}) {context : ECtx} {type : ETm 0}
    (proof : inhabits context type) : inhabitsIn model context type :=
  let ⟨term, wf, typing⟩ := proof
  ⟨wf, fun env satisfies => ⟨term.denote model env Fin.elim0, (typing.sound model env satisfies).2⟩⟩

theorem inhabitance_le_semanticInhabitance {Name : Type} (store : Store Name) (model : SetHierarchy.{u}) :
    inhabitance store ≤ semanticInhabitance store model :=
  system_mono (fun _ _ proof => inhabits_sound model proof)

theorem inhabitedTypes_subset_nonemptyTypes {Name : Type} (store : Store Name)
    (model : SetHierarchy.{u}) (context : ECtx) : inhabitedTypes store context ⊆ nonemptyTypes store model context :=
  ty.namesWhere_mono store (fun _ proof => inhabits_sound model proof)

end Silmaril.ProofFormats.DaslSyntax.MLTT
