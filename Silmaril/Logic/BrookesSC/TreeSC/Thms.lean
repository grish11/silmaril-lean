module

public import Silmaril.Logic.BrookesSC.TreeSC.Defs
public import Silmaril.Logic.BrookesSC.Concrete.Thms
public import Silmaril.Semantics.Brookes.StoreEquiv.Thms
public import Silmaril.Semantics.Brookes.TreeSC.Closed.Thms
import Silmaril.Proofs.Logic.BrookesSC.TreeSC.Comparison

public section

namespace Silmaril.Logic.BrookesSC.TreeSC

open CategoryTheory Silmaril.Semantics.Brookes
open Silmaril.Semantics.Brookes.TreeSC (Code Store treeBehavior treeBehavior_code denote_completes_iff_sc)
open Silmaril.Semantics.TrackA.Interaction (WeakITree)
open Silmaril.Semantics.TrackA.Concurrency (sc Config Shared)

variable {R X : Type} {S T : Signature (world R)}

/-- Encoding commutes with every designation-preserving label map in this world. -/
theorem encode_translate (labels : signature R ⟶ S) (f : S ⟶ T) (code : Code R) :
    (encode labels code).translate f = encode (labels ≫ f) code :=
  Proofs.Logic.BrookesSC.TreeSC.encode_translate labels f code

theorem inequation_translate (labels : signature R ⟶ S) (f : S ⟶ T) (lhs rhs : X → Code R) :
    (inequation labels lhs rhs).translate f = inequation (labels ≫ f) lhs rhs :=
  Proofs.Logic.BrookesSC.TreeSC.inequation_translate labels f lhs rhs

variable [DecidableEq R]

/-- Evaluation agrees on all closed words, including words with store gaps. -/
theorem eval_encode (labels : signature R ⟶ S) (M : Concrete.TraceModel S) (code : Code R) :
    M.eval (encode labels code) =
      (treeBehavior WeakITree.unfold code.toTree).transport (storeEquiv R) :=
  (Proofs.Logic.BrookesSC.TreeSC.eval_encode_denote labels M code).trans
    (congrArg (Behavior.transport (storeEquiv R)) (treeBehavior_code code).symm)

/-- The same comparison holds after relabeling, with the model reduced on the source side. -/
theorem eval_encode_reduct (labels : signature R ⟶ S) (f : S ⟶ T)
    (M : Concrete.TraceModel T) (code : Code R) :
    M.eval (encode (labels ≫ f) code) = (M.reduct f).eval (encode labels code) := by
  rw [← encode_translate]
  exact Concrete.eval_translate f M _

/-- Concrete satisfaction is exactly inclusion of completed tree words at each input. -/
theorem satisfies_iff (labels : signature R ⟶ S) (M : Concrete.TraceModel S)
    (lhs rhs : X → Code R) :
    (inequation labels lhs rhs).Satisfies M ↔
      ∀ (x : X) (word : Trace (Store R)),
        (treeBehavior WeakITree.unfold (lhs x).toTree).accepts word () →
        (treeBehavior WeakITree.unfold (rhs x).toTree).accepts word () :=
  Proofs.Logic.BrookesSC.TreeSC.satisfies_iff labels M lhs rhs

theorem satisfies_reduct (labels : signature R ⟶ S) (f : S ⟶ T) (M : Concrete.TraceModel T)
    (lhs rhs : X → Code R) :
    (inequation (labels ≫ f) lhs rhs).Satisfies M ↔
      (inequation labels lhs rhs).Satisfies (M.reduct f) := by
  rw [← inequation_translate]
  exact Concrete.satisfaction f M _

/-- Singleton concrete words recover contiguous completion in Track A's one-thread scheduler. -/
theorem eval_encode_completes_iff_sc (labels : signature R ⟶ S) (M : Concrete.TraceModel S)
    (code : Code R) (s t : Store R) :
    (M.eval (encode labels code)).completes (storeEquiv R s) (storeEquiv R t) () ↔
      ∃ events, sc.MTr (Config.single (code, Shared.initial s)) events
        (Config.single (.done, Shared.initial t)) := by
  rw [eval_encode, Behavior.transport_completes_iff, treeBehavior_code]
  exact denote_completes_iff_sc

end Silmaril.Logic.BrookesSC.TreeSC
