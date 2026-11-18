module

public import Silmaril.Machine.Vex.X86.MovJump.Defs
public import Silmaril.Machine.Vex.Validate.Defs
import Silmaril.Proofs.Machine.Vex.X86.MovJump

public section

namespace Silmaril.Machine.Vex.AMD64Scalar.MovJump

open Silmaril.Semantics.Region
open Silmaril.X86 (MState)
open Silmaril.Machine.Region.X86 (system)

theorem Fragment.decode_code (fragment : Fragment) : fragment.code.decode? 2 = some fragment.listing :=
  Proofs.decode fragment

theorem Fragment.decode_scalar (fragment : Fragment) :
    X86.decode fragment.base fragment.bytes = .ok fragment.block := Proofs.scalarDecode fragment

/-- Composable model map with real loaded memory as an invariant. -/
def Fragment.realization (fragment : Fragment) (guard : fragment.Guard) (completion : Bool) (ret : Word) :
    Realizes fragment.simple (system ret) := Proofs.realizes fragment guard completion ret

theorem Fragment.realization_relates (fragment : Fragment) (guard : fragment.Guard) (completion : Bool) (ret : Word)
    (input : Input) (full : MState) :
    (fragment.realization guard completion ret).relates input full ↔ fragment.Related completion input full := Iff.rfl

/-- The simple model has a normal exit, not UB or a missing behavior. -/
theorem Fragment.simple_exit (fragment : Fragment) (guard : fragment.Guard) {input : Input}
    (entry : input.rip = fragment.base) :
    ExitsNormally fragment.simple fragment.support input [] (fragment.block.run input) :=
  Proofs.smallGuard fragment guard entry

/-- The full machine retires through the cut to a unique normal exit. The
output relation is a projection and a loading invariant, not a state frame. -/
theorem Fragment.full_exit (fragment : Fragment) (guard : fragment.Guard) (completion : Bool) (ret : Word)
    {input : Input} {initial : MState} (entry : input.rip = fragment.base)
    (related : fragment.Related completion input initial) :
    ∃ final, ExitsNormally (system ret) fragment.support initial [] final ∧
      fragment.Related completion (fragment.block.run input) final :=
  Proofs.fullExit fragment guard completion ret entry related

/-- Lift a scalar postcondition to every full first exit, with separate
progress, termination and absence of a fault or other halt inside the cut. -/
theorem Fragment.lift_postcondition (fragment : Fragment) (guard : fragment.Guard) (completion : Bool) (ret : Word)
    {input : Input} {initial : MState} (entry : input.rip = fragment.base)
    (related : fragment.Related completion input initial) (property : List Empty → Input → Prop)
    (proved : property [] (fragment.block.run input)) :
    (∃ final, ExitsNormally (system ret) fragment.support initial [] final) ∧
    ∀ trace final, FirstExit (system ret) fragment.support initial trace final →
      property trace (project completion final) :=
  Proofs.postcondition fragment guard completion ret entry related property proved

theorem Fragment.region_sound (fragment : Fragment) (guard : fragment.Guard) (ret : Word) :
    Sound (system ret) (fun initial => initial.core.rip = fragment.base ∧ fragment.code.LoadedIn initial.memory)
      fragment.support (· = fragment.target.toNat) := Proofs.regionSound fragment guard ret

/-- Checker acceptances for these bytes compose with the real-model bridge.
The full first exit is guaranteed independently of target execution. -/
theorem Fragment.validated_exit (fragment : Fragment) (guard : fragment.Guard) (completion : Bool) (ret : Word)
    {raw : Raw.Block} {pair : Pair} (accepted : validate fragment.base fragment.bytes raw = .ok pair)
    {initial : MState} (entry : initial.core.rip = fragment.base) (loaded : fragment.code.LoadedIn initial.memory) :
    ∃ final, ExitsNormally (system ret) fragment.support initial [] final ∧
      pair.target.run (project completion initial) = .ok (project completion final) :=
  Proofs.validatedExit fragment guard completion ret accepted entry loaded

end Silmaril.Machine.Vex.AMD64Scalar.MovJump
