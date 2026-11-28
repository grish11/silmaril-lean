module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureGamma.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PurePrefix.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.PureRow.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Renaming.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.PurePrefix.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureGamma.Proofs

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open NestedTheta (Term)
open NestedTheta.ExplicitRuntime.PurePrefix (primitive_denote pure_denote gamma_denote)
open OrderedTheta (point carriedData)
open PurePrefix (orderedCall orderedCall_denote)
open PureRow (Segment Output encodeExit)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A P B C : τ}

theorem region_denote (s : Branch Φ ε A P B C)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) (env : Env [Choice A]) :
    Region.denote (ε := ε) (m := StateT σ Part.{u}) s.typing env =
      match TypeModel.coprodEquiv A A env.2 with
      | .inl x => Region.denote (ε := ε) (m := StateT σ Part.{u}) s.left.typing (PUnit.unit, x)
      | .inr x => Region.denote (ε := ε) (m := StateT σ Part.{u}) s.right.typing (PUnit.unit, x) := by
  have l := (Region.denote_spec (ε := ε) (m := StateT σ Part.{u}) s.left.typing).renameVars armEntry
  have r := (Region.denote_spec (ε := ε) (m := StateT σ Part.{u}) s.right.typing).renameVars armEntry
  have h := RegionDenotes.case (Denotes.var (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})
    (Γ := [Choice A]) (i := 0) (A := Choice A) rfl) l r
  rw [TwoBlock.regionDenote_eq_of coherent (show RegionDenotes (m := StateT σ Part.{u}) ε s.typing _ from h)]
  simp only [pure_bind, Env.rename, Env.get, id_eq]
  cases TypeModel.coprodEquiv A A env.2 <;> rfl

private theorem arm_denote (s : Segment Φ ε A P B C) (pureFirst : Bool)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (x : TyDen A) (token : σ) :
    (arm s pureFirst).1.denoteOpenWith (model (Φ := Φ) (ε := ε) (σ := σ)) (point x token) PUnit.unit =
      Part.map (encodeExit (P := P) (C := C))
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) s.typing (PUnit.unit,x)).run token) := by
  rw [s.region_denote coherent]
  cases pureFirst <;>
    simp only [arm, primitive_denote, pure_denote]
  all_goals
    change ((OrderedModel (τ := τ) (Φ := Φ) (ε := ε) (σ := σ)).primitive
      (.ordered (carriedData A) (carriedData B) (orderedCall s.first)) (point x token)).bind _ = _
    rw [orderedCall_denote, Part.bind_map]
    simp only [StateT.run_bind, Part.bind_eq_bind, Part.map_bind]
    congr 1
    funext first
    obtain ⟨_, middle⟩ := first
    change ((OrderedModel (τ := τ) (Φ := Φ) (ε := ε) (σ := σ)).primitive
      (.ordered (carriedData A) (carriedData C) (orderedCall s.second)) (point x middle)).bind _ = _
    rw [orderedCall_denote, Part.bind_map]
    congr 1
    funext last
    obtain ⟨out, final⟩ := last
    change Part.some (PureRow.output (PureRow.pureCall (σ := σ) s.value s.bottom x) out final) =
      Part.map encodeExit ((pure (.inl ((TypeModel.productEquiv P C).symm
        (PureRow.pureCall (σ := σ) s.value s.bottom x, out))) :
        StateT σ Part.{u} (LabelDen [Silmaril.product P C])).run final)
    simp [encodeExit, StateT.run_pure, Part.pure_eq_some]

private theorem result_eta (r : Tuple (OrderedRuntime.Structured.RuntimeValues (TyDen (τ := τ)) σ) (Output P C)) :
    PureRow.output (r.get .head) (r.get (.tail .head)) (r.get (.tail (.tail .head))) = r := by
  cases r with
  | cons a tail =>
    cases tail with
    | cons b tail =>
      cases tail with
      | cons c tail => cases tail; rfl

theorem agrees (s : Branch Φ ε A P B C) (pureFirst : Bool)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [Choice A]) (token : σ) :
    NestedTheta.Partial.observe (model (Φ := Φ) (ε := ε) (σ := σ)) (s.compile pureFirst) (entry env.2 token) =
      Part.map (encodeExit (P := P) (C := C))
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) s.typing env).run token) := by
  rw [region_denote s coherent]
  unfold NestedTheta.Partial.observe Branch.compile
  rw [NestedTheta.Term.toTerm_toGraph (s.code pureFirst).1]
  simp only [Branch.code, gamma_denote, Term.denoteOpenWith, entry]
  cases h : TypeModel.coprodEquiv A A env.2 with
  | inl x =>
    change ((arm s.left pureFirst).1.denoteOpenWith (model (Φ := Φ) (ε := ε) (σ := σ))
      (point x token) PUnit.unit).bind _ = _
    rw [← arm_denote s.left pureFirst coherent x token]
    simp only [Part.pure_eq_some, Part.bind_some_eq_map]
    exact Part.map_id' result_eta _
  | inr x =>
    change ((arm s.right true).1.denoteOpenWith (model (Φ := Φ) (ε := ε) (σ := σ))
      (point x token) PUnit.unit).bind _ = _
    rw [← arm_denote s.right true coherent x token]
    simp only [Part.pure_eq_some, Part.bind_some_eq_map]
    exact Part.map_id' result_eta _

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureGamma.Proofs
