module

public import Silmaril.Wasm.Logic.Reachability.WasmExpr.Defs

@[expose] public section
namespace Silmaril.Logic.Reachability.WasmExpr
open Silmaril.Logic.Institution.Examples
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Logic.Algebraic.Initial.Wasm (signature arithmetic)
open Silmaril.Wasm.Logic.Core (exec exec1 exec_append exec_cons exec_nil)

/-- The open expression compiler agrees with EQ evaluation, for every older
operand stack and every store/frame satisfying the explicit local environment. -/
theorem exec_code {H : Type} {k : Nat} (locals : Fin k → LocalIdx)
    (values : Fin k → BitVec 32) {u : Unit}
    (t : EQ.Term signature (fun _ : Fin k => ()) u) :
    ∀ (s : Store H) (f : Frame), LocalsAgree f locals values → ∀ rs : List Val,
      exec s f rs (code locals t) =
        some (s, f, Val.i32 (t.eval arithmetic values) :: rs) := by
  refine EQ.Term.rec (motive := fun _ t => ∀ (s : Store H) (f : Frame),
    LocalsAgree f locals values → ∀ rs : List Val,
      exec s f rs (code locals t) =
        some (s, f, Val.i32 (t.eval arithmetic values) :: rs)) ?_ ?_ t
  · intro i s f agree rs
    change exec s f rs [.localGet (locals i)] = some (s, f, Val.i32 (values i) :: rs)
    rw [exec_cons]
    simp only [exec1, agree i, Option.map_some, exec_nil]
  · intro n w u op args ih s f agree rs
    cases op with
    | literal x => rfl
    | add =>
      change exec s f rs ((code locals (args 0) ++ code locals (args 1)) ++
        [.intBinOp .i32 .add]) = _
      rw [List.append_assoc, exec_append, ih 0 s f agree]
      dsimp only
      rw [exec_append, ih 1 s f agree]
      rfl

end Silmaril.Logic.Reachability.WasmExpr
