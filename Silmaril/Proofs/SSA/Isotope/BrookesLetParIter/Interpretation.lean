module

public import Silmaril.SSA.Isotope.BrookesLetParIter.Defs
import Silmaril.Logic.BrookesSC.Concrete.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.BrookesLetParIter

open Silmaril.Isotope.BrookesLetParIter
open Silmaril.Logic.BrookesSC
open Silmaril.Semantics.Brookes

theorem pure_instruction_iff (op : Instr) :
    (instrEff op : Bool) = ⊥ ↔ op = .identity := by
  cases op <;> constructor <;> intro h <;> cases h <;> rfl

theorem abort_empty {A : Type} (p : M Empty) :
    p.bind (fun e : Empty => e.elim) = (⊥ : M A) := by
  apply Behavior.ext
  intro trace result
  refine ⟨fun h => ?_, False.elim⟩
  obtain ⟨_, _, e, _, _, _⟩ := Behavior.bind_accepts_iff.mp h
  exact e.elim

theorem acquire_free (thread : Bool) (n : Nat) :
    (eval (.acquire thread) ()).completes (state n none) (state n (some thread)) () := by
  exact (Concrete.primitive_completes_iff (W := world) (.acquire thread ()) _ _ _).mpr rfl

theorem acquire_held (thread owner : Bool) (n : Nat) (t : Store) :
    ¬(eval (.acquire thread) ()).completes (state n (some owner)) t () := by
  intro h
  have step := (Concrete.primitive_completes_iff (W := world) (.acquire thread ()) _ _ _).mp h
  simp [Concrete.Store.step, state] at step

theorem release_owner (thread : Bool) (n : Nat) :
    (eval (.release thread) ()).completes (state n (some thread)) (state n none) () := by
  apply (Concrete.primitive_completes_iff (W := world) (.release thread ()) _ _ _).mpr
  cases thread <;> rfl

theorem release_nonowner (thread owner : Bool) (hne : owner ≠ thread) (n : Nat) (t : Store) :
    ¬(eval (.release thread) ()).completes (state n (some owner)) t () := by
  intro h
  have step := (Concrete.primitive_completes_iff (W := world) (.release thread ()) _ _ _).mp h
  cases owner <;> cases thread <;> first | exact hne rfl | cases step

end Silmaril.Proofs.SSA.Isotope.BrookesLetParIter
