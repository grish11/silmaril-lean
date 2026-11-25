module

public import Silmaril.Wasm.Examples.Sha256FullRound.Defs
import Silmaril.Proofs.Wasm.Examples.Sha256FullRound.Arithmetic
import Silmaril.Proofs.Wasm.Examples.Sha256FullRound.Memory
import Silmaril.Proofs.Wasm.Examples.Sha256FullRound.Exec

public section
namespace Silmaril.Wasm.Examples.Sha256FullRound

open Execution.Core SingleThreaded SingleThreaded.Det SingleThreaded.Exec
open Silmaril.Crypto.SHA256.Kernel (Word)

/-- The pinned bytes decode to the checked signatures, bodies, memory and exports. -/
theorem decode_fixture : decodeShape? fixture = some artifactShape :=
  Proofs.Wasm.Examples.Sha256FullRound.decode_fixture

/-- The compiled e body returns the fifth FIPS working word without altering state. -/
theorem run_e {H : Type} (o : GrowOracle) (x : Input) (d : Word) (s : Store H)
    (mi : ModuleInst) :
    runI o (eBody.length + 1) (eEntry x d s mi) =
      (⟨s, (eEntry x d s mi).frame, [constI32 (outputWords x d)[4]]⟩, true) :=
  Proofs.Wasm.Examples.Sha256FullRound.run_e o x d s mi

/-- The eight stores leave all bytes outside the destination slice intact. -/
theorem round_output (dst : Nat) (words : Vector Word 8) (before : ByteArray)
    (bounds : dst + 32 ≤ before.size) :
    OutputOk before (roundMemory dst words before) dst words :=
  Proofs.Wasm.Examples.Sha256FullRound.round_output dst words before bounds

/-- The compiled void wrapper returns to the same caller frame. Its store effect
is confined to the eight consecutive little-endian output words in memory 0. -/
theorem call_round {H : Type} (o : GrowOracle) (dst : Word) (x : Input) (d : Word)
    (s : Store H) (caller : Frame) (mi : ModuleInst) (index : FuncIdx)
    (calleeAddr address : Nat) (mem : MemInst)
    (wrapperSlot : caller.module.funcs[index.toNat]? = some calleeAddr)
    (wrapperCode : s.funcs[calleeAddr]? = some (roundInstance mi))
    (links : Linkage s mi) (mapped : s.mem? {module := mi} ⟨0⟩ = some (address, mem))
    (bounds : dst.toNat + 32 ≤ mem.bytes.size)
    (typedA : ConfigOk (Sha256Round.entry x s mi) [.i32])
    (typedE : ConfigOk (eEntry x d (s.setMem address (memoryAfterA dst x d mem)) mi) [.i32]) :
    let bytes := roundMemory dst.toNat (outputWords x d) mem.bytes
    Steps (profile o) noHost ⟨s, caller, vals (roundValues dst x d) ++ expression [.call index]⟩
      ⟨s.setMem address {mem with bytes := bytes}, caller, []⟩ ∧
    OutputOk mem.bytes bytes dst.toNat (outputWords x d) :=
  Proofs.Wasm.Examples.Sha256FullRound.call_round o dst x d s caller mi index calleeAddr address
    mem wrapperSlot wrapperCode links mapped bounds typedA typedE

end Silmaril.Wasm.Examples.Sha256FullRound
