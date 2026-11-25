module

public import Silmaril.Wasm.Examples.Sha256FullRound.Defs
import Silmaril.Wasm.Verify.Kernel.Thms
meta import Silmaril.Wasm.Verify.Kernel.Defs

public section
namespace Silmaril.Proofs.Wasm.Examples.Sha256FullRound

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.SingleThreaded.Exec Silmaril.Wasm.Verify.Kernel
open Silmaril.Wasm.Examples.Sha256FullRound
open Silmaril.Crypto.SHA256.Kernel

set_option maxRecDepth 12000 in
theorem decode_fixture : decodeShape? fixture = some artifactShape := by
  kernel_rfl

private theorem choose_eq (e f g : Word) :
    ((g ^^^ f) &&& e) ^^^ g = Ch e f g := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [Ch, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not, hi,
    decide_true, Bool.true_and]
  cases e.getLsbD i <;> cases f.getLsbD i <;> cases g.getLsbD i <;> rfl

private theorem rotate_eq (x : Word) (n : Nat) (hn : 0 < n) (hw : n < 32) :
    x.rotateLeft (32 - n) = x.rotateRight n := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i _
  simp only [BitVec.getLsbD_rotateLeft, BitVec.getLsbD_rotateRight,
    Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt (show 32 - n < 32 by omega),
    show 32 - (32 - n) = n by omega]

private def compiledE (x : Input) (d : Word) : Word :=
  let sigma := x.e.rotateLeft 26 ^^^ x.e.rotateLeft 21 ^^^ x.e.rotateLeft 7
  let choose := ((x.g ^^^ x.f) &&& x.e) ^^^ x.g
  x.h + d + sigma + x.k + choose + x.w

private theorem compiledE_eq (x : Input) (d : Word) :
    compiledE x d = (outputWords x d)[4] := by
  change compiledE x d = d + (x.h + Sigma1 x.e + Ch x.e x.f x.g + x.k + x.w)
  unfold compiledE Sigma1
  rw [choose_eq, rotate_eq x.e 6 (by decide) (by decide),
    rotate_eq x.e 11 (by decide) (by decide), rotate_eq x.e 25 (by decide) (by decide)]
  dsimp only
  ac_rfl

set_option maxRecDepth 6000 in
private theorem run_compiledE {H : Type} (o : GrowOracle) (x : Input) (d : Word)
    (s : Store H) (mi : ModuleInst) :
    runIK o (eBody.length + 1) (eEntry x d s mi) =
      (⟨s, (eEntry x d s mi).frame, [constI32 (compiledE x d)]⟩, true) := by
  kernel_rfl

theorem run_e {H : Type} (o : GrowOracle) (x : Input) (d : Word) (s : Store H)
    (mi : ModuleInst) :
    runI o (eBody.length + 1) (eEntry x d s mi) =
      (⟨s, (eEntry x d s mi).frame, [constI32 (outputWords x d)[4]]⟩, true) := by
  rw [← runIK_eq, run_compiledE, compiledE_eq]

end Silmaril.Proofs.Wasm.Examples.Sha256FullRound
