module

public import Silmaril.Wasm.Logic.Algebraic.Initial.Wasm
public import Silmaril.Logic.Reachability.Finite.Thms
public import Silmaril.Logic.Reachability.Relational

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Reachability.WasmExpr
open Silmaril.Logic.Institution.Examples
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Logic.Algebraic.Initial.Wasm (signature arithmetic Operation)

/-- Open terms reuse the actual public EQ syntax and literal/add signature. -/
abbrev Expr (k : Nat) := EQ.Term signature (fun _ : Fin k => ()) ()

/-- A caller selects local indices; distinct source variables may share a local
provided the explicit environment agreement below holds. -/
def code {k : Nat} (locals : Fin k → LocalIdx) {u : Unit} :
    EQ.Term signature (fun _ : Fin k => ()) u → List Instr
  | .var i => [.localGet (locals i)]
  | .app (.literal x) _ => [.intConst .i32 x]
  | .app .add args => code locals (args 0) ++ code locals (args 1) ++ [.intBinOp .i32 .add]

/-- Each declared variable has an existing initialized local containing its assigned i32. -/
def LocalsAgree {k : Nat} (f : Frame) (locals : Fin k → LocalIdx)
    (values : Fin k → BitVec 32) : Prop :=
  ∀ i, Silmaril.Wasm.Logic.Core.localVal? f (locals i) = some (Val.i32 (values i))

def start {H : Type} {k : Nat} (s : Store H) (f : Frame) (rs : List Val)
    (locals : Fin k → LocalIdx) (t : Expr k) (rest : List Admin) : Config H :=
  ⟨s, f, vals rs.reverse ++ expression (code locals t) ++ rest⟩

def finish {H : Type} {k : Nat} (s : Store H) (f : Frame) (rs : List Val)
    (values : Fin k → BitVec 32) (t : Expr k) (rest : List Admin) : Config H :=
  ⟨s, f, vals (Val.i32 (t.eval arithmetic values) :: rs).reverse ++ rest⟩

/-- A predicate-valued target permits exact source/run correspondence and
impossible-target controls without an execution determinism assumption. -/
def predicateModel {H : Type} (P : Profile) (host : HostSemantics H)
    (initial : Config H) (target : Config H → Prop) : Model () (relationalSignature Bool) :=
  @relationalModel Bool (Config H) ⟨initial⟩ (Step P host)
    (fun flag => {c | if flag then target c else c = initial})

/-- The target relation is the pinned native Core step, without a phase encoding.
Atoms select the exact initial and desired final configuration. -/
def model {H : Type} (P : Profile) (host : HostSemantics H)
    (initial target : Config H) : Model () (relationalSignature Bool) :=
  @relationalModel Bool (Config H) ⟨target⟩ (Step P host)
    (fun flag => {c | c = if flag then target else initial})

end Silmaril.Logic.Reachability.WasmExpr
