module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Model.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Kleisli.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Body
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Graph
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Kleisli

/-! # Exact preservation and reflection of partial state observations -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open OrderedTheta (point)
open Silmaril.Elgot (iter)

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
namespace Wiring

open OrderedTheta (point)
open OrderedRuntime.Structured
open TwoBlock.TwoExit (Pure)
open LinearChain.Wiring (newest)

variable {B : τ} {args ins out outs : Ports (OrderedRuntime.Structured.Ty τ)}
variable {past : List (Ports (OrderedRuntime.Structured.Ty τ))}
variable {a : Data args} {o : Data outs}
variable {live : Origin (Threaded args) past runtime}

local notation "readWire" => OrderedRuntime.Structured.readOrigin (F := WireValues (τ := τ) (σ := σ))

omit [TypeFormers τ] [Isotope.Subtyping τ] [TypeModel τ] in
theorem read_newest {F : OrderedRuntime.Structured.Ty τ → Type u}
    {t : OrderedRuntime.Structured.Ty τ} (p : Port out t)
    (entry : Tuple F args) (locals : Locals F past) (outcome : Tuple F out) :
    OrderedRuntime.Structured.readOrigin (newest p past) entry (locals.snoc outcome) = outcome.get p :=
  Proofs.read_newest p entry locals outcome

omit [TypeFormers τ] [Isotope.Subtyping τ] [TypeModel τ] in
theorem read_nextRuntime {F : OrderedRuntime.Structured.Ty τ → Type u}
    (entry : Tuple F args) (locals : Locals F past) (outcome : Tuple F (Threaded out)) :
    OrderedRuntime.Structured.readOrigin (nextRuntime past out) entry (locals.snoc outcome) =
      outcome.get (runtimePort out) :=
  Proofs.read_nextRuntime entry locals outcome

theorem eval_primitive (i : Data ins) (d : Data out) (op : Instruction (Pure τ) (Effect Φ) ins out)
    (inputs : Wires (Threaded args) past ins) (rest : Code Φ a o (nextRuntime past out))
    (entry : Tuple (WireValues (τ := τ) (σ := σ)) (Threaded args))
    (locals : Locals (WireValues (τ := τ) (σ := σ)) past) :
    eval (ε := ε) (Wiring.primitive i d op live inputs rest) entry locals =
      (wireModel (ε := ε) (σ := σ)).primitive (.ordered i d op)
        (Wires.read (withRuntime live inputs) entry locals) >>= fun output =>
      eval (ε := ε) rest entry (locals.snoc output) :=
  Proofs.eval_primitive i d op inputs rest entry locals

theorem eval_finish (source : Origin (Threaded args) past (.value B))
    (entry : Tuple (WireValues (τ := τ) (σ := σ)) (Threaded args))
    (locals : Locals (WireValues (τ := τ) (σ := σ)) past) :
    eval (ε := ε) (Wiring.finish (Φ := Φ) (a := a) past live source) entry locals =
      Part.some (point (readWire source entry locals) (readWire live entry locals)) :=
  Proofs.eval_finish source entry locals

theorem eval_choice (i : Data ins) (d : Data out)
    (left right : Code (past := []) Φ i d (.arg (runtimePort ins)))
    (selector : Origin (Threaded args) past (.control 2))
    (inputs : Wires (Threaded args) past ins) (rest : Code Φ a o (nextRuntime past out))
    (entry : Tuple (WireValues (τ := τ) (σ := σ)) (Threaded args))
    (locals : Locals (WireValues (τ := τ) (σ := σ)) past) :
    eval (ε := ε) (Wiring.choice i d left right selector live inputs rest) entry locals =
      eval (ε := ε) (past := []) (Fin.cases left (fun _ => right) (readWire selector entry locals).down)
        (Wires.read (withRuntime live inputs) entry locals) PUnit.unit >>= fun output =>
      eval (ε := ε) rest entry (locals.snoc output) :=
  Proofs.eval_choice i d left right selector inputs rest entry locals

end Wiring

variable {A B K E D : τ}
variable {r : Isotope.LambdaSSA.Region Φ} {g : Graph Φ A E D}

/-- The acyclic subgraph retains the data result and exact returned token. -/
theorem body_observe (b : Body Φ A B) (x : TyDen A) (token : σ) :
    (Wiring.body b).2.1.denoteOpenWith (wireModel (ε := ε) (σ := σ)) (point x token) PUnit.unit =
      Part.map (fun p => point p.1 p.2) ((bodyAction (ε := ε) (m := StateT σ Part.{u}) b x).run token) :=
  Proofs.body_denote b x token

theorem graph_observe (s : Loop Φ A B K E D) (a : TyDen A) (initial : σ) :
    observe (ε := ε) (graph s) a initial =
      Part.map (exitTuple (A := A)) ((iter (round (ε := ε) (m := StateT σ Part.{u}) s) a).run initial) :=
  Proofs.graph_observe s a initial

/-- A θ entered at a completed carrier passes it through with the same
token. Its header instruction and body actions are skipped. -/
theorem graph_completed (s : Loop Φ A B K E D) (out : TyDen E ⊕ TyDen D) (token : σ) :
    NestedTheta.Partial.observe (wireModel (ε := ε)) (graph s)
      (point (TwoBlock.TwoExit.finish out) token) =
      Part.some (point (TwoBlock.TwoExit.finish out) token) :=
  Proofs.graph_completed s out token

/-- Interpret the actual flat loop by iterating its typed activation. -/
theorem denote_rounds (s : Loop Φ A B K E D)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) :
    Region.denote (ε := ε) (m := StateT σ Part.{u}) (Theta.regionTyping s) env =
      iter (round (ε := ε) (m := StateT σ Part.{u}) s) env.2 :=
  Proofs.region_round_eq s coherent env

/-- Equality of partial observations at the actual LambdaSSA boundary. -/
theorem Related.region_observe (w : Related A B K E D r g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial =
      Part.map (exitTuple (A := A)) ((Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial) := by
  cases w with
  | loop s => rw [denote_rounds s coherent env]; exact graph_observe s env.2 initial

theorem exitTuple_injective :
    Function.Injective (exitTuple (A := A) (E := E) (D := D) (σ := σ)) :=
  Proofs.exitTuple_injective

/-- A finite graph return has exactly the decoded label, its typed payload,
and the final state observed by the actual LambdaSSA region. -/
theorem Related.region_returns_iff (w : Related A B K E D r g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (label : LabelDen [E,D]) (initial final : σ) :
    returns (ε := ε) g env.2 initial label final ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial = Part.some (label, final) :=
  Proofs.returns_of_observe g env.2 initial final label _ (w.region_observe coherent env initial)

/-- An undefined partial observation on either side is undefined on both. -/
theorem Related.region_undefined_iff (w : Related A B K E D r g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.none ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial = Part.none := by
  rw [w.region_observe coherent env initial]
  exact Proofs.map_none_iff _ _

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime
