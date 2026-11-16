module

public import Silmaril.Logic.Algebraic.Initial.Thms
public import Silmaril.Wasm.Logic.Core.Thms

/-! A constructor-only instruction-expression algebra for i32 literals and add.
The unique fold is connected to the actual native straight-line interpreter
and then to its existing Core small-step soundness theorem. -/
@[expose] public section
namespace Silmaril.Logic.Algebraic.Initial.Wasm
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core

inductive Operation : (n : Nat) → (Fin n → Unit) → Unit → Type where
  | literal (x : BitVec 32) : Operation 0 (fun _ => ()) ()
  | add : Operation 2 (fun _ => ()) ()

abbrev signature : EQ.Signature := ⟨Unit, Operation⟩
abbrev Expr := EQ.Term signature (closedContext signature) ()

abbrev arithmetic : EQ.Algebra signature where
  carrier _ := BitVec 32
  op o args := match o with
    | .literal x => x
    | .add => args 0 + args 1

def evaluate : closedAlgebra signature ⟶ arithmetic := foldHom arithmetic (fun i => i.elim0)

theorem evaluate_unique (f : closedAlgebra signature ⟶ arithmetic) : f = evaluate :=
  (closed_isInitial signature).hom_ext _ _

def code {s : Unit} : EQ.Term signature (closedContext signature) s → List Instr
  | .var i => i.elim0
  | .app (.literal x) _ => [.intConst .i32 x]
  | .app .add args => code (args 0) ++ code (args 1) ++ [.intBinOp .i32 .add]

/-- The actual native interpreter evaluates compiled terms on any operand tail. -/
theorem exec_code {H : Type} {u : Unit} (t : EQ.Term signature (closedContext signature) u)
    : ∀ (s : Store H) (f : Frame) (rs : List Val),
    exec s f rs (code t) =
      some (s, f, Val.i32 (t.eval arithmetic (fun i => i.elim0)) :: rs) := by
  refine EQ.Term.rec (motive := fun _ t => ∀ (s : Store H) (f : Frame) (rs : List Val),
    exec s f rs (code t) =
      some (s, f, Val.i32 (t.eval arithmetic (fun i => i.elim0)) :: rs))
    (fun i => i.elim0) ?_ t
  intro n w u o args ih s f rs
  cases o with
  | literal x => rfl
  | add =>
    change exec s f rs ((code (args 0) ++ code (args 1)) ++ [.intBinOp .i32 .add]) = _
    rw [List.append_assoc, exec_append, ih 0]
    dsimp only
    rw [exec_append, ih 1]
    rfl

/-- Existing interpreter soundness supplies an actual pinned Core run, for every
profile and host semantics, with arbitrary stores, frames and operand tails. -/
theorem executes {H : Type} (P : Profile) (host : HostSemantics H)
    (s : Store H) (f : Frame) (rs : List Val) (t : Expr) :
    Steps P host ⟨s, f, vals rs.reverse ++ expression (code t) ++ []⟩
      ⟨s, f, vals (Val.i32 (evaluate.map () t) :: rs).reverse ++ []⟩ :=
  exec_sound [] (exec_code t s f rs)

def lit (x : BitVec 32) : Expr := .app (.literal x) (fun i => i.elim0)
def add (a b : Expr) : Expr := .app .add (Fin.cases a (fun _ => b))

theorem wrapping_example : evaluate.map () (add (lit (4294967295#32)) (lit (1#32))) = 0#32 := by
  decide

end Silmaril.Logic.Algebraic.Initial.Wasm
