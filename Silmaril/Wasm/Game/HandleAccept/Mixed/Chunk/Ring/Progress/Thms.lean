module

public import Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Ring.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.RingLive

public section

namespace Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Ring

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

/-- A full `feed` in the growth-backed module has a finite Core reduction to a
call-local trap for every profile. The reduction cannot reach either the allocator
or any host import and leaves the entire persistent store unchanged. -/
theorem chunkRingGrowing_feed_full {cap : Nat} (capacity : RingCap cap)
    {buffer : List (BitVec 64)} {store : Store Nat} (invariant : growingRingInv cap buffer store)
    (full : buffer.length = cap) (input : BitVec 64) (profile : Profile) (host : HostSemantics Nat) :
    Steps profile host (invoke store 4 [.i64 input]) ⟨store, {}, [.trap]⟩ :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.RingLive.growing_feed_full capacity invariant full input

end Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Ring
