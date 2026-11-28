module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PurePrefix.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.Executable.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.PureRow.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.PurePrefix.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Renaming.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PurePrefix.Proofs

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open Sequential
open OrderedTheta (point pack carried carriedData)
open OrderedRuntime.Structured (Threaded withRuntime)
open TwoBlock.TwoExit (enter Carrier)
open NestedTheta.ExplicitRuntime.PurePrefix (primitive_denote pure_denote attach_denote)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A R B X Z L E D : τ} {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

theorem region_denote (setup : Prefix Φ ε A R B) (body : Source Φ B X Z L E D sigs)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) (env : Env [A]) :
    Region.denote (ε := ε) (m := StateT σ Part.{u}) (typing setup body) env =
      TwoBlock.call (ε := ε) setup.action env.2 >>= fun _ =>
        Region.denote (ε := ε) (m := StateT σ Part.{u}) body.fragment.typing
          (PUnit.unit, PureRow.pureCall (σ := σ) setup.value setup.bottom env.2) := by
  have tail := (Region.denote_spec (ε := ε) (m := StateT σ Part.{u}) body.fragment.typing).renameVars
    (keepEntry (R := R) (A := A))
  have spec := RegionDenotes.let₁ (PureRow.typingAt_denotes (ε := ε) (σ := σ) setup.action (Γ := [A]) (i := 0) rfl)
    (.let₁ (PureRow.typingAt_denotes (ε := ε) (σ := σ) setup.value (Γ := [R,A]) (i := 1) rfl) tail)
  rw [TwoBlock.regionDenote_eq_of coherent (show RegionDenotes (m := StateT σ Part.{u}) ε (typing setup body) _ from spec)]
  simp only [PureRow.call_bottom setup.value setup.bottom, pure_bind, Env.rename, Env.get, id_eq]

theorem orderedCall_denote (p : TwoBlock.Instruction Φ A R) (x : TyDen A) (initial : σ) :
    (Wires.wireModel (Φ := Φ) (ε := ε) (σ := σ)).primitive
      (.ordered (carriedData A) (carriedData R) (orderedCall p))
      (point x initial) =
      Part.map (fun (y, token) => point y token) ((TwoBlock.call (ε := ε) (m := StateT σ Part.{u}) p x).run initial) := by
  change Part.map OrderedRuntime.Structured.decode
    (((TwoBlock.call (ε := ε) (m := StateT σ Part.{u}) p x >>= fun y => pure (pack y)).run initial)) = _
  simp only [StateT.run_bind, Part.bind_eq_bind, StateT.run_pure, Part.pure_eq_some,
    Part.bind_some_eq_map, Part.map_map]
  rfl

theorem graph_denote (setup : Prefix Φ ε A R B) (body : Source Φ B X Z L E D sigs)
    (pureFirst : Bool) (x : TyDen A) (initial : σ) :
    NestedTheta.Partial.observe (model (Φ := Φ) (ε := ε) (σ := σ))
        (compile setup body pureFirst) (point x initial) =
      ((TwoBlock.call (ε := ε) (m := StateT σ Part.{u}) setup.action x).run initial).bind fun result =>
        Flat.Serial.observe (ε := ε) (Translation.compile body)
          (PureRow.pureCall (σ := σ) setup.value setup.bottom x) result.2 := by
  unfold NestedTheta.Partial.observe compile
  rw [NestedTheta.Term.toTerm_toGraph]
  cases pureFirst <;> simp only [code, pure_denote, primitive_denote, attach_denote]
  all_goals
    change ((Wires.wireModel (Φ := Φ) (ε := ε) (σ := σ)).primitive
      (.ordered (carriedData A) (carriedData R) (orderedCall setup.action))
      (point x initial)).bind _ = _
    rw [orderedCall_denote, Part.bind_map]
    rfl

theorem agrees (setup : Prefix Φ ε A R B) (body : Source Φ B X Z L E D sigs)
    (pureFirst : Bool)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    NestedTheta.Partial.observe (model (Φ := Φ) (ε := ε) (σ := σ))
        (compile setup body pureFirst) (point env.2 initial) =
      Part.map (ExplicitRuntime.exitTuple (A := L))
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) (typing setup body) env).run initial) := by
  rw [graph_denote, region_denote setup body coherent, StateT.run_bind, Part.bind_eq_bind, Part.map_bind]
  congr 1
  funext result
  exact body.compile_observe coherent (PUnit.unit, PureRow.pureCall (σ := σ) setup.value setup.bottom env.2) result.2

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PurePrefix.Proofs
