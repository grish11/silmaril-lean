module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Splice.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Proofs

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open OrderedTheta (point carriedData resultData)
open OrderedRuntime.Structured (decode)
open TwoBlock.TwoExit (Carrier ExitCode enter finish)
open NestedTheta.ExplicitRuntime.Splice (append_denote)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A X Y H M E D : τ}
variable {ps qs : List (Ports (OrderedRuntime.Structured.Ty τ))}

private def classify (exit : LabelDen [E,M]) (token : σ) :=
  (Wires.wireModel (Φ := Φ) (ε := ε)).primitive
    (.ordered (carriedData (Carrier H E M)) (resultData (Carrier M E D)) (.effect .routeExit))
    (ExplicitRuntime.exitTuple (A := H) (exit, token))

private theorem classify_first (e : TyDen E) (token : σ) :
    classify (Φ := Φ) (ε := ε) (H := H) (M := M) (D := D) (.inl e) token =
      Part.some (decode (ExplicitRuntime.choiceData (X := ExitCode E D) (Y := M)
        (.inl ((TypeModel.coprodEquiv E D).symm (.inl e))), token)) := by
  change Part.map (decode (ts := OrderedTheta.results (Carrier M E D)))
    (((Wires.model (Φ := Φ) (ε := ε)).effect .routeExit
      (.cons (finish (A := H) (.inl e : TyDen E ⊕ TyDen M)) .nil)).run token) = _
  simp only [Wires.model, finish, Equiv.apply_symm_apply]
  rfl

private theorem classify_second (input : TyDen M) (token : σ) :
    classify (Φ := Φ) (ε := ε) (H := H) (E := E) (D := D) (.inr (.inl input)) token =
      Part.some (decode (ExplicitRuntime.choiceData (X := ExitCode E D) (Y := M) (.inr input), token)) := by
  change Part.map (decode (ts := OrderedTheta.results (Carrier M E D)))
    (((Wires.model (Φ := Φ) (ε := ε)).effect .routeExit
      (.cons (finish (A := H) (.inr input : TyDen E ⊕ TyDen M)) .nil)).run token) = _
  simp only [Wires.model, finish, Equiv.apply_symm_apply]
  rfl

private theorem repack (p : Tuple (OrderedRuntime.Structured.RuntimeValues (TyDen (τ := τ)) σ)
    (WirePorts M E D)) :
    point (p.get .head) (p.get (.tail .head)) = p := by
  cases p with
  | cons value tail =>
    cases tail with
    | cons token tail => cases tail; rfl

private theorem select_agrees (q : Code Φ M E D M E D qs)
    {right : Fragment Φ M E D} (hq : Agrees (ε := ε) (σ := σ) right q.1.toGraph)
    (exit : LabelDen [E,M]) (token : σ) :
    (select q).1.denoteOpenWith (Wires.wireModel (ε := ε))
      (ExplicitRuntime.exitTuple (A := H) (exit, token)) PUnit.unit =
      Part.map (ExplicitRuntime.exitTuple (A := M))
        ((Sum.elim pure (fun input =>
          Region.denote (ε := ε) (m := StateT σ Part.{u}) right.typing (PUnit.unit,input))
            ((routing (E := E) (M := M) (D := D)).select exit)).run token) := by
  unfold select
  rw [NestedTheta.Term.denoteOpenWith, Part.bind_eq_bind]
  change (classify (Φ := Φ) (ε := ε) (H := H) (D := D) exit token).bind _ = _
  rcases exit with e | input | impossible
  · rw [classify_first, Part.bind_some, NestedTheta.Term.denoteOpenWith, Part.bind_eq_bind]
    change (Part.some (ExplicitRuntime.exitTuple (A := M) ((.inl e : LabelDen [E,D]), token))).bind _ =
      Part.map (ExplicitRuntime.exitTuple (A := M)) (Part.some ((.inl e : LabelDen [E,D]), token))
    rw [Part.bind_some, Part.map_some]
    rfl
  · rw [classify_second, Part.bind_some, NestedTheta.Term.denoteOpenWith, Part.bind_eq_bind]
    let result := q.1.denoteOpenWith (Wires.wireModel (ε := ε)) (point (enter input) token) PUnit.unit
    change result.bind (fun p => Part.some (point (p.get .head) (p.get (.tail .head)))) = _
    have ret : (fun p : Tuple (OrderedRuntime.Structured.RuntimeValues (TyDen (τ := τ)) σ)
        (WirePorts M E D) => Part.some (point (p.get .head) (p.get (.tail .head)))) = Part.some :=
      funext fun p => congrArg Part.some (repack p)
    calc
      _ = result.bind Part.some := congrArg result.bind ret
      _ = result := Part.bind_some_right result
      _ = _ := by
        have agreed := hq (PUnit.unit, input) token
        simp only [observe, NestedTheta.Partial.observe, NestedTheta.Term.toTerm_toGraph] at agreed
        exact agreed
  · exact impossible.elim

theorem splice_agrees (p : Code Φ A X Y H E M ps) (q : Code Φ M E D M E D qs)
    {left : Fragment Φ A E M} {right : Fragment Φ M E D}
    (hp : Agrees (ε := ε) (σ := σ) left p.1.toGraph) (hq : Agrees (ε := ε) (σ := σ) right q.1.toGraph)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) :
    Agrees (ε := ε) (σ := σ) (Flat.linkBy left right routing) (splice p q).1.toGraph := by
  intro env initial
  have head := hp env initial
  simp only [observe, NestedTheta.Partial.observe, NestedTheta.Term.toTerm_toGraph] at head ⊢
  rw [splice, append_denote, head, Flat.denote_linkBy _ _ _ coherent, StateT.run_bind]
  simp only [Part.bind_eq_bind, Part.bind_map, Part.map_bind]
  congr 1
  funext outcome
  exact select_agrees q hq outcome.1 outcome.2

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Proofs
