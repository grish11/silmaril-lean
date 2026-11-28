module

public import Silmaril.Machine.SeaOfNodes.Diamond.RTL.Defs
import Silmaril.Proofs.Machine.SeaOfNodes.Diamond.RTL.Correctness

/-! # Return correspondence for the word diamond -/

public section

namespace Silmaril.Machine.SeaOfNodes.Diamond.RTL

open Silmaril.Machine.Lir (Memory Word)

variable {sigs : List (List PortTy)}

open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA (Block Prog StepsNWithin)
open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow Val read)
open Silmaril.SSA.RVSDG (Origin Port Tuple extend)

/-- The existing producer emitter executes one machine step per typed producer,
preserving memory and resolving every typed read in the resulting frame. -/
theorem emitOpsWith_steps {ports : List PortTy} (argReg : ∀ {t}, Port ports t → Reg)
    (separate : ∀ {t} (p : Port ports t) (i : Nat), argReg p ≠ .node i)
    (input : Tuple (Val model.value) ports) (flow : Dataflow WordOp ports [] sigs)
    (fr : Frame Reg) (mem : Memory) (prog : Prog Reg) (func label : Nat) (block : Block Reg)
    (found : prog.block? func label = some block) (code : block.ops = emitOpsWith (fun p => argReg p) flow)
    (agree : ∀ {t} (p : Port ports t), fr.get (argReg p) = some (encodeValue t (input.get p))) :
    ∃ ready, StepsNWithin prog [] sigs.length ⟨⟨func, label, 0⟩, fr, [], mem⟩
      ⟨⟨func, label, sigs.length⟩, ready, [], mem⟩ ∧
      ∀ {t} (wire : Origin ports (extend [] sigs) t),
        ready.get (registerWith (fun p => argReg p) wire) =
          some (encodeValue t (read model wire input (flow.eval model input PUnit.unit))) :=
  Proofs.emitOpsWith_steps argReg separate input flow fr mem prog func label block found code agree

/-- The whole-program RTL return exists exactly for the source return word.
The RTL observation also fixes the result arity and preserves the input memory. -/
theorem lower_returns_iff (g : WordDiamond sigs) (x y : Word) (initial final : Memory)
    (returned : List Word) :
    (lower g).oracle 0 [x, y] initial returned final ↔
      ∃ value : Word, g.Returns model (entry x y) value ∧ returned = [value] ∧ final = initial :=
  Proofs.lower_returns_iff g x y initial final returned

/-- Every edge emitted by the lowering goes to a strictly greater block label. -/
theorem lower_forward (g : WordDiamond sigs) {source target : Nat}
    (h : target ∈ (lowerFunc g).succ source) : source < target :=
  Proofs.lower_forward g h

end Silmaril.Machine.SeaOfNodes.Diamond.RTL
