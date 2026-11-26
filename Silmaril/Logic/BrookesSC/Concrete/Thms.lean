module

public import Silmaril.Logic.BrookesSC.Concrete.Defs
public import Silmaril.Logic.BrookesSC.Thms
public import Silmaril.Semantics.Brookes.Thms
import Silmaril.Proofs.Logic.BrookesSC.Concrete.Interpretation

@[expose] public section

namespace Silmaril.Logic.BrookesSC.Concrete

open CategoryTheory Silmaril.Semantics.Brookes

universe u

variable {W : World.{u}}
variable {S T : Signature W} {A B : Type u}

theorem bind_mono {x y : Behavior (Store W) A} {k l : A → Behavior (Store W) B}
    (h : Includes x y) (hk : ∀ a, Includes (k a) (l a)) : Includes (x.bind k) (y.bind l) :=
  Proofs.Logic.BrookesSC.Concrete.bind_mono h hk

variable [DecidableEq W.Cell] [DecidableEq W.Mutex] [DecidableEq W.Thread]

/-- Every carrier consists of closed sets of nonempty Brookes words and replies. -/
abbrev target (W : World.{u}) [DecidableEq W.Cell] [DecidableEq W.Mutex] [DecidableEq W.Thread] :
    Target.{u,u} W where
  Carrier := Behavior (Store W)
  order _ :=
    { le := Includes
      le_refl _ := fun {_ _} h => h
      le_trans _ _ _ h₁ h₂ := fun {_ _} h => h₂ (h₁ h) }
  pure := Behavior.ret
  bind := Behavior.bind
  primitive := primitive
  bind_mono := bind_mono

/-- A model chooses the Brookes behavior for each external label. -/
abbrev TraceModel (S : Signature W) := Model (target W) S

/-- The fixed-world institution of SC program inclusion on Brookes traces. -/
def institution (W : World.{u}) [DecidableEq W.Cell] [DecidableEq W.Mutex] [DecidableEq W.Thread] :
    Signature W ⥤ Silmaril.Logic.Institution.Room :=
  BrookesSC.institution (target W)

theorem primitive_accepts_iff (p : Primitive W) (trace : Trace (Store W)) (reply : p.Reply) :
    (primitive p).accepts trace reply ↔
      ∃ s t, Store.step p s = some (reply, t) ∧ Reduces [(s, t)] trace :=
  Behavior.atomic_accepts_iff

theorem primitive_completes_iff (p : Primitive W) (s t : Store W) (reply : p.Reply) :
    (primitive p).completes s t reply ↔ Store.step p s = some (reply, t) :=
  Behavior.atomic_completes_iff

theorem primitive_load_mode (thread : W.Thread) (cell : W.Cell) :
    primitive (.load thread .plain cell) = primitive (.load thread .scAtomic cell) := rfl

theorem primitive_store_mode (thread : W.Thread) (cell : W.Cell) (value : W.Value cell) :
    primitive (.store thread .plain cell value) = primitive (.store thread .scAtomic cell value) := rfl

theorem eval_ret (M : TraceModel S) (value : A) :
    M.eval (.ret value) = Behavior.ret value := by
  rw [Model.eval]

theorem eval_call_external (M : TraceModel S) {sort : W.ExternalSort} (op : S.Op (.external sort))
    (next : W.ExternalReply sort → Program S A) :
    M.eval (.call op next) = (M.external op).bind (fun reply => M.eval (next reply)) := by
  rw [Model.eval, Model.operation]

theorem eval_call_primitive (M : TraceModel S) {p : Primitive W} (op : S.Op (.primitive p))
    (next : p.Reply → Program S A) :
    M.eval (.call op next) = (primitive p).bind (fun reply => M.eval (next reply)) := by
  rw [Model.eval, Model.operation]

theorem eval_call_primitive_ret (M : TraceModel S) {p : Primitive W} (op : S.Op (.primitive p)) :
    M.eval (.call op Program.ret) = primitive p := by
  rw [eval_call_primitive]
  exact Behavior.bind_ret (primitive p)

/-- One legal primitive generator followed by an accepted continuation word.
The stores on either side of the join may differ. -/
theorem eval_call_primitive_accepts_iff (M : TraceModel S) {p : Primitive W}
    (op : S.Op (.primitive p)) (next : p.Reply → Program S A)
    (trace : Trace (Store W)) (value : A) :
    (M.eval (.call op next)).accepts trace value ↔
      ∃ s t reply tail, Store.step p s = some (reply, t) ∧ (M.eval (next reply)).accepts tail value ∧
        Reduces ([(s, t)] ++ tail) trace := by
  rw [eval_call_primitive]
  exact Proofs.Logic.BrookesSC.Concrete.primitive_bind_accepts_iff p _ trace value

theorem eval_translate (f : S ⟶ T) (M : TraceModel T) (program : Program S A) :
    M.eval (program.translate f) = (M.reduct f).eval program :=
  Model.eval_translate f M program

theorem reduct_external (f : S ⟶ T) (M : TraceModel T) {sort : W.ExternalSort}
    (op : S.Op (.external sort)) : (M.reduct f).external op = M.external (f.label op) := rfl

theorem eval_mono {M N : TraceModel S} (h : M ⟶ N) (program : Program S A) :
    Includes (M.eval program) (N.eval program) :=
  Model.eval_mono h program

theorem satisfies_iff (M : TraceModel S) (e : Sentence S) :
    e.Satisfies M ↔ ∀ x, Includes (M.eval (e.lhs x)) (M.eval (e.rhs x)) := Iff.rfl

theorem satisfaction (f : S ⟶ T) (M : TraceModel T) (e : Sentence S) :
    (e.translate f).Satisfies M ↔ e.Satisfies (M.reduct f) :=
  Sentence.satisfaction f M e

end Silmaril.Logic.BrookesSC.Concrete
