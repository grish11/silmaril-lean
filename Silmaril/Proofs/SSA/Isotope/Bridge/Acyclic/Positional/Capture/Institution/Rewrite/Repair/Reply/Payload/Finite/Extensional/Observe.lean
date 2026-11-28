module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Extensional.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.CommonRequest.Thms

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.Extensional

open Kleisli (value)
open LambdaSSA (At)
open LambdaSSA.Region (packedExitType)
open LambdaSSA.Semantics.Categorical (labelAt_get)
open LetIter.Semantics.Categorical (boundEnv)
open Silmaril.Semantics.NondeterministicTrace (Tagged)

set_option backward.isDefEq.respectTransparency false

local notation "Γ₀" => (Ctx.nil : Ctx Empty Sorts)

private theorem request_trace {L : List Sorts} (req : Bool) (l r : Bool → Path L) :
    (Path.request req (l false) (l true) (r false) (r true)).traceTree =
      requestTree req (fun b => (l b).traceTree) (fun b => (r b).traceTree) := rfl

private theorem trace_specialize {L : List Sorts} {n : Nat} (p : Normal L n) (env : Assignment n) :
    (specialize p env).traceTree = p.traceTree env := by
  induction p with
  | ret => rfl
  | emit b p ih => exact congrArg (Reply.Normal.emit b) (ih env)
  | request req l r ihl ihr =>
    change (Path.request req (specialize l (env.push false)) (specialize l (env.push true))
      (specialize r (env.push false)) (specialize r (env.push true))).traceTree =
      requestTree req (fun b => l.traceTree (env.push b)) (fun b => r.traceTree (env.push b))
    exact (request_trace req (fun b => specialize l (env.push b)) (fun b => specialize r (env.push b))).trans
      (congrArg₂ (requestTree req) (funext fun b => ihl (env.push b)) (funext fun b => ihr (env.push b)))
  | testRequest test low lf lr hf hr ilf ilr ihf ihr =>
    cases h : env test
    · simp only [specialize, Normal.traceTree, h, Bool.false_eq_true, ite_false]
      exact (request_trace low (fun b => specialize lf ((env.without test).push b))
        (fun b => specialize lr ((env.without test).push b))).trans
        (congrArg₂ (requestTree low) (funext fun b => ilf _) (funext fun b => ilr _))
    · simp only [specialize, Normal.traceTree, h, ite_true]
      exact (request_trace (!low) (fun b => specialize hf ((env.without test).push b))
        (fun b => specialize hr ((env.without test).push b))).trans
        (congrArg₂ (requestTree (!low)) (funext fun b => ihf _) (funext fun b => ihr _))

private theorem trace_common {L : List Sorts} {n : Nat} (p : CommonRequest.NormalSource L n)
    (test : Fin (n + 1)) (env : Assignment (n + 1)) :
    (commonNormal p test env).traceTree = p.traceTree test env := by
  have branch (l r : Normal L (n + 1)) :=
    (request_trace p.request (fun b => specialize l ((env.without test).push b))
      (fun b => specialize r ((env.without test).push b))).trans
      (congrArg₂ (requestTree p.request) (funext fun b => trace_specialize l _)
        (funext fun b => trace_specialize r _))
  cases h : env test
  · simp only [commonNormal, CommonRequest.NormalSource.traceTree, h, Bool.false_eq_true, ite_false]
    exact branch p.arms.falseLeft p.arms.falseRight
  · simp only [commonNormal, CommonRequest.NormalSource.traceTree, h, ite_true]
    exact branch p.arms.trueLeft p.arms.trueRight

theorem path_trace_inj_proof (L : List Sorts) : Function.Injective (@Path.traceTree L) := by
  intro p
  induction p with
  | ret pos b =>
    intro q h
    cases q with
    | ret pos' b' =>
      obtain ⟨rfl, rfl⟩ := Position.result_inj (Reply.Normal.ret.inj h)
      rfl
    | emit | request => cases h
  | emit b p ih =>
    intro q h
    cases q with
    | emit b' q =>
      obtain ⟨rfl, sub⟩ := Reply.Normal.emit.inj h
      rw [ih sub]
    | ret | request => cases h
  | request req lf lt rf rt ilf ilt irf irt =>
    intro q h
    cases q with
    | request req' lf' lt' rf' rt' =>
      change requestTree req _ _ = requestTree req' _ _ at h
      obtain ⟨label, left, right⟩ := requestTree_inj h
      have e₁ : lf = lf' := ilf (left false)
      have e₂ : lt = lt' := ilt (left true)
      have e₃ : rf = rf' := irf (right false)
      have e₄ : rt = rt' := irt (right true)
      rw [label, e₁, e₂, e₃, e₄]
    | ret | emit => cases h

theorem programOutcomes_eq_of_sat_proof (H : Sorts) (L : List Sorts) {n : Nat}
    (p q : Source (H :: L) n)
    (h : ((LetCase.inst Γ₀).obj signature).Sat (Kleisli.algebra model) (grammarCase (equation H L p q)))
    (env : Assignment n) :
    programOutcomes H L p env = programOutcomes H L q env :=
  congrArg Tagged.outcomes (Kleisli.run_eq_of_sat model (equation H L p q) h (CommonRequest.packedAssignment n env))

private theorem packed_normal_run (H : Sorts) (L : List Sorts) {n : Nat} (p : Normal (H :: L) n)
    (env : Assignment n) :
    programOutcomes H L (.tree p.render) env = p.outcomes env := by
  let T := packedExitType (H :: L)
  let ρ := boundEnv value (CommonRequest.packedAssignment n env)
  let body := ((program H L (.tree p.render)).body.render .base).encode.toLetCase.2
  let finish (x : value T) := Kleisli.run model body (ρ.snoc (A := T) x)
  have ret (x : Exits.Exit (H :: L)) : finish x.packed = pure x.packed :=
    Exits.run_router model (rfl : At (H :: L) 0 H) (H :: L) (LambdaSSA.Ren.id (H :: L))
      .base ρ x.1 (labelAt_get (H :: L) x.1) x.2
  exact p.run _ ρ env (CommonRequest.bitSlots_matches n env) finish ret

theorem tree_programOutcomes_proof (H : Sorts) (L : List Sorts) {n : Nat}
    (t : Tree (H :: L) n) (env : Assignment n) :
    programOutcomes H L (.tree t) env = t.normal.outcomes env := by
  have normalize : Derivable false (equation H L (.tree t) (.tree t.normal.render)) :=
    .let₁ (t.replay (CommonRequest.bitSlots n))
      (.refl ((program H L (.tree t)).body.render .base).encode.toLetCase.2.toHasType)
  have sat := Kleisli.sat_of_repaired model model_respectsPure _ (Repaired.ofNative normalize)
  exact (programOutcomes_eq_of_sat_proof H L (.tree t) (.tree t.normal.render) sat env).trans
    (packed_normal_run H L t.normal env)

theorem programOutcomes_proof (H : Sorts) (L : List Sorts) {n : Nat}
    (p : Source (H :: L) n) (env : Assignment n) :
    programOutcomes H L p env = (p.normal env).traceTree.outcomesWith Exits.Exit.packed := by
  cases p with
  | tree t =>
    exact (tree_programOutcomes_proof H L t env).trans
      (congrArg (Reply.Normal.outcomesWith Exits.Exit.packed) (trace_specialize t.normal env).symm)
  | common test t =>
    exact (CommonRequest.programOutcomes_eq H L test t env).trans
      (congrArg (Reply.Normal.outcomesWith Exits.Exit.packed) (trace_common t.normal test env).symm)

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.Extensional
