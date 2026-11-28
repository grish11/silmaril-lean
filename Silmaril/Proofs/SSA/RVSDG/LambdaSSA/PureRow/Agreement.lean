module

public import Silmaril.SSA.RVSDG.LambdaSSA.PureRow.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.Thms
import Mathlib.Tactic.FinCases

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.PureRow.Proofs

open Isotope.LambdaSSA (Region Tm)
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open OrderedTheta (point)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ ε σ : Type u} [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
variable {A P B C : τ}

theorem relocate (s : Segment Φ ε A P B C) :
    NestedTheta.Graph.Isomorphic (Op Φ ε) s.early.toGraph s.late.toGraph := by
  refine .intro rfl rfl (Equiv.swap (0 : Fin 3) 1) ?_ ?_ ?_ ?_
  · intro i
    fin_cases i <;> rfl
  · intro i
    fin_cases i <;> rfl
  · rfl
  · intro i j
    fin_cases i <;> exact j.elim0

theorem effect_order (s : Segment Φ ε A P B C) (ids : Fin 3 ≃ Fin 3)
    (movesFirst : ids 1 = 2) :
    ¬ ∀ i, (s.early.toGraph.nodes i).inputs.addresses.map (Address.rename (renameVertex ids)) =
      (s.early.toGraph.nodes (ids i)).inputs.addresses := by
  intro inputs
  have moved := inputs 1
  rw [movesFirst] at moved
  change [Address.arg 0, Address.arg 1] = [Address.arg 0, Address.output 1 1] at moved
  cases moved

variable [TypeFormers τ] [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]

theorem callAt (p : TwoBlock.Instruction Φ A C) {Γ : List τ} {i : Nat} (hi : Γ[i]? = some A) :
    Denotes (m := StateT σ Part.{u}) ε (typingAt p hi) (fun env => TwoBlock.call (ε := ε) p (Env.get env i hi)) := by
  obtain ⟨op, ha, hc⟩ := p
  subst A
  subst C
  have applied := Denotes.op (m := StateT σ Part.{u}) (ε := ε) (Denotes.var (Φ := Φ) hi)
  convert applied using 1
  funext env
  unfold TwoBlock.call
  rw [pure_bind, bind_pure]

theorem call_bottom (p : TwoBlock.Instruction Φ A P) (h : (instrEff p.op : ε) = ⊥) (x : TyDen A) :
    TwoBlock.call (ε := ε) (m := StateT σ Part.{u}) p x = pure (pureCall (σ := σ) p h x) := by
  obtain ⟨op, ha, hb⟩ := p
  subst A
  subst P
  simp [TwoBlock.call, pureCall, denotePureInstr, InstructionModel.denote_pure op h]

theorem flat_run (s : Segment Φ ε A P B C)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) (env : Env [A]) :
    Region.denote (ε := ε) (m := StateT σ Part.{u}) s.typing env =
      (TwoBlock.call (ε := ε) s.first env.2 >>= fun _ =>
        TwoBlock.call (ε := ε) s.second env.2 >>= fun result =>
          pure (.inl ((TypeModel.productEquiv P C).symm (pureCall (σ := σ) s.value s.bottom env.2, result)))) := by
  have spec := RegionDenotes.let₁ (ε := ε) (m := StateT σ Part.{u}) (callAt (ε := ε) (σ := σ) s.value (Γ := [A]) (i := 0) rfl)
    (.let₁ (callAt (ε := ε) (σ := σ) s.first (Γ := [P,A]) (i := 1) rfl)
      (.let₁ (callAt (ε := ε) (σ := σ) s.second (Γ := [B,P,A]) (i := 2) rfl)
        (.br (h := (rfl : ([Silmaril.product P C] : List τ)[0]? = some (Silmaril.product P C)))
          (.pair (.var (i := 2) (rfl : ([C,B,P,A] : List τ)[2]? = some P))
            (.var (i := 0) (rfl : ([C,B,P,A] : List τ)[0]? = some C))))))
  rw [TwoBlock.regionDenote_eq_of coherent (show RegionDenotes (m := StateT σ Part.{u}) ε s.typing _ from spec)]
  simp only [call_bottom s.value s.bottom, pure_bind, Env.get, labelInject_eq_recursive, LabelValue.inject]

theorem agrees (s : Segment Φ ε A P B C)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    NestedTheta.Partial.observe (model (Φ := Φ) (ε := ε) (σ := σ)) s.early.toGraph (point env.2 initial) =
      Part.map (encodeExit (P := P) (C := C))
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) s.typing env).run initial) := by
  rw [flat_run s coherent]
  unfold NestedTheta.Partial.observe
  rw [NestedTheta.Term.toTerm_toGraph]
  let value := pureCall (σ := σ) s.value s.bottom env.2
  simp only [Segment.early, dataRow, orderedRow, NestedTheta.Term.denoteOpenWith, NestedTheta.Kind.denoteWith,
    model, point, Wires.read, Locals.get, Locals.snoc, Part.bind_eq_bind]
  change (Part.some (.cons value .nil :
    Tuple (OrderedRuntime.Structured.RuntimeValues (TyDen (τ := τ)) σ) (OrderedTheta.carried P))).bind _ = _
  rw [Part.bind_some]
  change (Part.map (fun r : TyDen B × σ => point r.1 r.2)
    ((TwoBlock.call (ε := ε) (m := StateT σ Part.{u}) s.first env.2).run initial)).bind _ = _
  rw [Part.bind_map]
  simp only [StateT.run_bind, Part.bind_eq_bind, Part.map_bind]
  congr 1
  funext first
  obtain ⟨_, middle⟩ := first
  change (Part.map (fun r : TyDen C × σ => point r.1 r.2)
    ((TwoBlock.call (ε := ε) (m := StateT σ Part.{u}) s.second env.2).run middle)).bind _ = _
  rw [Part.bind_map]
  congr 1
  funext last
  obtain ⟨out, final⟩ := last
  change Part.some (output value out final) =
    Part.map encodeExit ((pure (.inl ((TypeModel.productEquiv P C).symm (value, out))) :
      StateT σ Part.{u} (LabelDen [Silmaril.product P C])).run final)
  simp [encodeExit, StateT.run_pure, Part.pure_eq_some]


omit [HasTy Φ τ] [HasEff Φ ε] [Bot ε] [InstructionModel Φ τ ε (StateT σ Part.{u})] in
theorem encodeExit_injective : Function.Injective (encodeExit (τ := τ) (σ := σ) (P := P) (C := C)) := by
  rintro ⟨left, s⟩ ⟨right, t⟩ same
  rcases left with a | dead
  · rcases right with b | dead
    · have values : (TypeModel.productEquiv P C) a = (TypeModel.productEquiv P C) b :=
        Prod.ext (congrArg (fun x => x.get .head) same) (congrArg (fun x => x.get (.tail .head)) same)
      exact Prod.ext (congrArg Sum.inl ((TypeModel.productEquiv P C).injective values))
        (congrArg (fun x => x.get (.tail (.tail .head))) same)
    · exact dead.elim
  · exact dead.elim

omit [HasTy Φ τ] [HasEff Φ ε] [Bot ε] [InstructionModel Φ τ ε (StateT σ Part.{u})] in
theorem mapped_exit_iff (result : Part (LabelDen [Silmaril.product P C] × σ))
    (exit : LabelDen [Silmaril.product P C]) (final : σ) :
    Part.map encodeExit result = Part.some (encodeExit (exit, final)) ↔ result = Part.some (exit, final) := by
  rw [Part.eq_some_iff, Part.mem_map_iff, Part.eq_some_iff]
  simp only [encodeExit_injective.eq_iff, exists_eq_right]

end Silmaril.SSA.RVSDG.LambdaSSA.PureRow.Proofs
