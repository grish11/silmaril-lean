module

public import Silmaril.SSA.RVSDG.MLIR.Regionless.Defs
public import Silmaril.SSA.RVSDG.Institution.Thms
public import Silmaril.SSA.MLIR.Institution.Thms
import Silmaril.SSA.RVSDG.ValueMap.Thms

public section

namespace Silmaril.SSA.RVSDG.MLIR.Regionless.Proofs

open CategoryTheory

variable {V St : Type} {P Q : Dialect V St} {L K : Silmaril.MLIR.Institution.Signature false}
variable {F G : PortType V St → Type}

theorem to_ofAssignment (ts : List V) (env : (i : Fin ts.length) → F (.value (ts.get i))) :
    toAssignment ts (ofAssignment ts env) = env := by
  induction ts with
  | nil => exact funext fun i => i.elim0
  | cons _ ts ih =>
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact congrFun (ih (fun i => env i.succ)) j

theorem of_toAssignment (ts : List V) (xs : Tuple F (valuePorts St ts)) :
    ofAssignment ts (toAssignment ts xs) = xs := by
  induction ts with
  | nil => cases xs; rfl
  | cons _ ts ih => cases xs with | cons x xs => exact congrArg (Tuple.cons x) (ih xs)

private theorem toAssignment_map (f : ∀ t, F t → G t)
    (ts : List V) (xs : Tuple F (valuePorts St ts)) (i : Fin ts.length) :
    toAssignment ts (xs.map f) i = f _ (toAssignment ts xs i) := by
  induction ts with
  | nil => exact i.elim0
  | cons _ ts ih =>
    cases xs with
    | cons x xs => exact Fin.cases rfl (ih xs) i

private theorem ofAssignment_map (f : ∀ t, F t → G t)
    (ts : List V) (env : (i : Fin ts.length) → F (.value (ts.get i))) :
    (ofAssignment ts env).map f = ofAssignment ts (fun i => f _ (env i)) := by
  induction ts with
  | nil => rfl
  | cons _ ts ih => exact congrArg (Tuple.cons (f _ (env 0))) (ih (fun i => env i.succ))

open Silmaril.MLIR.Institution (Assignment)

variable {args outs : List V} {sigs : List (Ports (PortType V St))}

private def denotePort (f : ProfileMap P L) (M : Silmaril.MLIR.Institution.Model L)
    (env : Assignment M.carrier (context f.sort args)) :
    (t : PortType V St) → (f.syntaxModel args).Val t → (f.pullback M).Val t
  | .value _, t => t.denote M env
  | .state _, x => x
  | .control _, x => x

set_option backward.isDefEq.respectTransparency false in
theorem denote_translateGraph (f : ProfileMap P L) (M : Silmaril.MLIR.Institution.Model L)
    (g : Graph P (valuePorts St args) [] sigs (valuePorts St outs))
    (env : Assignment M.carrier (context f.sort args)) (i : Fin outs.length) :
    (translateGraph f g i).denote M env =
      toAssignment outs (g.run (f.pullback M) (ofAssignment args env)) i := by
  have run := g.run_map (denotePort f M env)
    (entry := ofAssignment args Silmaril.MLIR.Institution.Term.var)
    (control := fun _ _ => rfl) (run := ?_)
  · calc
      _ = toAssignment outs ((g.run (f.syntaxModel args)
          (ofAssignment args Silmaril.MLIR.Institution.Term.var)).map (denotePort f M env)) i :=
        (toAssignment_map (denotePort f M env) outs _ i).symm
      _ = _ := by rw [run, ofAssignment_map]; rfl
  · intro ins outs op input
    simp only [ProfileMap.syntaxModel, ProfileMap.pullback, ProfileMap.interpret]
    generalize f.symbol op = s
    cases s with
    | symbol s =>
      simp only [MatchedOp.interpret]
      rw [ofAssignment_map]
      congr 1
      funext j
      change ((operationBlock s j).subst _).denote M env = _
      rw [Silmaril.MLIR.Institution.Term.denote_subst]
      simp only [operationBlock, Silmaril.MLIR.Institution.Term.denote]
      congr 1
      · funext k
        exact (toAssignment_map (denotePort f M env) _ input k).symm
      · exact funext fun r => r.elim0

set_option backward.isDefEq.respectTransparency false in
theorem satisfaction (f : ProfileMap P L) (M : Silmaril.MLIR.Institution.Model L)
    (e : ValueEquation P) :
    (translateEquation f e).Holds M ↔ e.toRVSDG.Holds (f.pullback M) := by
  change (∀ env, ∀ i, (translateGraph f e.lhs i).denote M env =
    (translateGraph f e.rhs i).denote M env) ↔ _
  simp only [denote_translateGraph]
  constructor
  · intro h input
    have pointwise := funext (h (toAssignment e.args input))
    rw [of_toAssignment] at pointwise
    exact (of_toAssignment _ _).symm.trans
      ((congrArg (ofAssignment e.outs) pointwise).trans (of_toAssignment _ _))
  · intro h env i
    exact congrArg (fun xs => toAssignment e.outs xs i) (h (ofAssignment e.args env))

set_option backward.isDefEq.respectTransparency false in
theorem translateGraph_precomp (f : ProfileMap Q L) (h : Institution.OpcodeMap P Q)
    (g : Graph P (valuePorts St args) [] sigs (valuePorts St outs)) :
    translateGraph (f.precomp h) g = translateGraph f (Institution.mapGraph h g) := by
  unfold translateGraph
  rw [Institution.mapGraph_run]
  rfl

private def mapPort (f : ProfileMap P L) (k : L ⟶ K) :
    (t : PortType V St) → (f.syntaxModel args).Val t → ((f.map k).syntaxModel args).Val t
  | .value _, t => t.map k
  | .state _, x => x
  | .control _, x => x

set_option backward.isDefEq.respectTransparency false in
theorem translateGraph_map (f : ProfileMap P L) (k : L ⟶ K)
    (g : Graph P (valuePorts St args) [] sigs (valuePorts St outs)) (i : Fin outs.length) :
    (translateGraph f g i).map k = translateGraph (f.map k) g i := by
  have run := g.run_map (mapPort f k)
    (entry := ofAssignment args Silmaril.MLIR.Institution.Term.var)
    (control := fun _ _ => rfl) (run := ?_)
  · calc
      _ = toAssignment outs ((g.run (f.syntaxModel args)
          (ofAssignment args Silmaril.MLIR.Institution.Term.var)).map (mapPort f k)) i :=
        (toAssignment_map (mapPort f k) outs _ i).symm
      _ = _ := by rw [run, ofAssignment_map]; rfl
  · intro ins outs op input
    simp only [ProfileMap.syntaxModel, ProfileMap.map, ProfileMap.interpret]
    generalize f.symbol op = s
    cases s with
    | symbol s =>
      simp only [MatchedOp.map, MatchedOp.interpret]
      rw [ofAssignment_map]
      congr 1
      funext j
      change ((operationBlock s j).subst _).map k = _
      have block_map : (operationBlock (L := L) s j).map k =
          operationBlock (L := K) (sort := k.sort ∘ f.sort) (k.symbol s) j := by
        simp only [operationBlock, Silmaril.MLIR.Institution.Term.map]
        congr 1
        exact funext fun r => r.elim0
      rw [Silmaril.MLIR.Institution.Term.map_subst, block_map]
      congr 1
      funext l
      exact (toAssignment_map (mapPort f k) _ input l).symm

set_option backward.isDefEq.respectTransparency false in
theorem pullback_map (f : ProfileMap P L) (k : L ⟶ K)
    (M : Silmaril.MLIR.Institution.Model K) :
    (f.map k).pullback M = f.pullback (M.reduct k) := by
  simp only [ProfileMap.pullback, ProfileMap.interpret, ProfileMap.map,
    Silmaril.MLIR.Institution.Model.reduct]
  congr 1
  funext ins outs op input
  cases f.symbol op
  rfl

end Silmaril.SSA.RVSDG.MLIR.Regionless.Proofs
