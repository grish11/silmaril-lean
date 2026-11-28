module

public import Silmaril.Machine.PEG.CountedLoop.Defs
public import Silmaril.SSA.PEG.Bridge.Theta.Region.MLIR.Thms
import Silmaril.Proofs.Machine.PEG.CountedLoop.Correctness

public section

namespace Silmaril.Machine.PEG.CountedLoop

open Silmaril.Machine.Lir (Word Memory)
open Silmaril.MLIR.Arith (Env)
open Silmaril.MLIR.Pure (Eval OpSignature)
open Silmaril.MLIR.SCF (While)
open Silmaril.SSA.PEG
open Silmaril.SSA.PEG.Bridge.Theta.Region.Ordered (Bundle)
open Silmaril.SSA.RVSDG (Port Tuple)

@[simp] theorem fromWords_words (input : Env Bank) : fromWords (words input) = some input :=
  Proofs.fromWords_words input

theorem words_injective : Function.Injective words :=
  Proofs.words_injective

theorem target_wellFormed : target.WellFormed := by decide

/-- Every successful machine execution returns exactly the source bank and
preserves all memory. Every finite SCF return is attained by a machine run. -/
theorem returns_iff_scf {Op : OpSignature} {loop : While Op Bank Bank}
    (image : Image loop) (evalOp : Eval Op) (agreement : image.Agrees evalOp)
    (input : Env Bank) (initial final : Memory) (values : List Word) :
    (∃ fuel, (lower image).runMain fuel 0 (words input) initial = .returned values final) ↔
      ∃ result : Env Bank, (∃ fuel, loop.run evalOp fuel input = some result) ∧
        values = words result ∧ final = initial :=
  Proofs.returns_iff_scf image evalOp agreement input initial final values

section Peggy

open Silmaril.SSA.PEG.Bridge.Theta.Region

variable {Data : Type} {P : InstructionSet.{0,0} Data} {left right : Data} {n : Nat}
variable {g : Graph P (pegSlots left right) (pegSlots left right) n 1} {t : Silmaril.SSA.PEG.Ty Data}
variable {slot : Port (pegSlots left right) t} {invariants : Bool}
variable (b : Bundle g slot invariants)
variable (evalOp : Eval (MLIR.Opcode (wordProfile Data) P))
variable (image : Image (MLIR.lower (wordProfile Data) b))
variable (agreement : image.Agrees evalOp)
variable (neg : ∀ flag : Bool,
  (MLIR.model (wordProfile Data) evalOp).run b.scalar.descriptor.negate (.cons ⟨flag⟩ .nil) = ⟨!flag⟩)

include agreement neg in
/-- The three ordered return words agree in both directions with the complete
Figure 11 observation at the common first exit of the checked loop. -/
theorem returns_iff_observe (input : Env Bank) (initial final : Memory) (values : List Word) (idx : Index 1) :
    let m := MLIR.model (wordProfile Data) evalOp
    let decode := (wordProfile Data).decode (pegSlots left right)
    (∃ fuel, (lower image).runMain fuel 0 (words input) initial = .returned values final) ↔
      ∃ result : Env Bank,
        g.observe m.toPEG (g.denote m.toPEG (decode input) b.demandWellFounded) idx =
          (decode result).map (fun _ => some) ∧ values = words result ∧ final = initial :=
  Proofs.returns_iff_observe b evalOp image agreement neg input initial final values idx

include agreement neg in
/-- Compare a specific ABI packet directly, using length and order to
recover the unique typed return bank. -/
theorem returns_iff_observe_bank (input result : Env Bank) (initial final : Memory) (idx : Index 1) :
    let m := MLIR.model (wordProfile Data) evalOp
    let decode := (wordProfile Data).decode (pegSlots left right)
    (∃ fuel, (lower image).runMain fuel 0 (words input) initial = .returned (words result) final) ↔
      g.observe m.toPEG (g.denote m.toPEG (decode input) b.demandWellFounded) idx =
        (decode result).map (fun _ => some) ∧ final = initial :=
  Proofs.returns_iff_observe_bank b evalOp image agreement neg input result initial final idx

include agreement neg in
/-- Successful machine execution witnesses one shared first pass and the
defined Figure 11 evaluation prefixes for all three result slots. -/
theorem firstExit_of_run (input : Env Bank) (initial final : Memory) (values : List Word) (idx : Index 1)
    (fuel : Nat) (ran : (lower image).runMain fuel 0 (words input) initial = .returned values final) :
    let m := MLIR.model (wordProfile Data) evalOp
    let decode := (wordProfile Data).decode (pegSlots left right)
    ∃ (result : Env Bank) (k : Nat) (finalBank : Tuple m.toPEG.Value (.bool :: pegSlots left right)),
      values = words result ∧ final = initial ∧ carriedValues finalBank = decode result ∧
        b.scalar.TraceObservation m.toPEG
          (g.denote m.toPEG (decode input) b.demandWellFounded) idx k finalBank :=
  Proofs.firstExit_of_run b evalOp image agreement neg input initial final values idx fuel ran

end Peggy
end Silmaril.Machine.PEG.CountedLoop
