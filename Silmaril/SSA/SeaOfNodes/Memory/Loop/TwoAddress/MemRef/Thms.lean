module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.MemRef.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Petri.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.MemRef.Correctness
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Petri.Thms

/-! Address decoding, exact CFG successors, and whole-buffer finite observations. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.MemRef

open RVSDG (Tuple)
open RVSDG.NestedTheta.Petri (Finishes)
open Silmaril.MLIR.Arith (Env)
open Silmaril.MLIR.CF.Ordered (Block)
open Silmaril.MLIR.MemRef (Buffer)

variable {cells : Nat} {args : List ValueSort}

theorem decodeAddress_encode (address : Address cells) :
    decodeAddress (encodeAddress address) = some address :=
  Proofs.decodeAddress_encode address

/-- A raw operand decodes to an address exactly when it is that
address's bit-vector encoding. -/
theorem decodeAddress_eq_some (value : BitVec (addressWidth cells).val) (address : Address cells) :
    decodeAddress value = some address ↔ value = encodeAddress address :=
  Proofs.decodeAddress_eq_some value address

theorem decodeAddresses_encode (first second : Address cells) :
    decodeAddresses (encodeAddresses first second) = some (first, second) :=
  Proofs.decodeAddresses_encode first second

/-- The admitted header frames are exactly the encodings of in-bounds pairs. -/
theorem decodeAddresses_eq_some (env : Env (headerTypes cells)) (first second : Address cells) :
    decodeAddresses env = some (first, second) ↔ env = encodeAddresses first second :=
  Proofs.decodeAddresses_eq_some env first second

theorem header_rejects (graph : Graph args) (input : Tuple (Val cells) args)
    (env : Env (headerTypes cells)) (buffer : Buffer cells) (invalid : decodeAddresses env = none) :
    (Block.eval (evalBody input) ((lower cells graph).block .header) env).run buffer = none :=
  Proofs.header_rejects graph input env buffer invalid

/-- Entry passes both source addresses and preserves the initialized buffer. -/
theorem entry_transition (graph : Graph args) (input : Tuple (Val cells) args) (heap : Heap cells) :
    (Block.eval (evalBody input) (lower cells graph).entry .nil).run ⟨heap⟩ =
      some (.inl ⟨Label.header,
        encodeAddresses (graph.seed input heap).first (graph.seed input heap).second⟩, ⟨heap⟩) :=
  rfl

/-- The actual header runs the emitted effects and guard. Its conditional
edge passes both old-bank selections on feedback or the word on exit,
with the complete post-store buffer in either case. -/
theorem header_transition (graph : Graph args) (input : Tuple (Val cells) args) (header : Header cells) :
    (Block.eval (evalBody input) ((lower cells graph).block .header)
      (encodeAddresses header.first header.second)).run ⟨header.heap⟩ =
      some (match graph.step input header with
        | .inl (word, final) => (.inl ⟨Label.exit, .cons word .nil⟩, ⟨final⟩)
        | .inr next => (.inl ⟨Label.header, encodeAddresses next.first next.second⟩, ⟨next.heap⟩)) :=
  Proofs.header_transition graph input header

/-- A finite result needs at least entry, one header, and exit. -/
theorem runFuel_eq_of_lt_three (graph : Graph args) (input : Tuple (Val cells) args)
    (fuel : Nat) (heap : Heap cells) (below : fuel < 3) :
    runFuel graph input fuel ⟨heap⟩ = none :=
  Proofs.runFuel_eq_of_lt_three graph input fuel heap below

/-- A native allowance of b backedges agrees with b + 3 CFG block steps. -/
theorem run_eq_evalWithin (graph : Graph args) (input : Tuple (Val cells) args)
    (budget : Nat) (heap : Heap cells) :
    run graph input budget ⟨heap⟩ =
      (graph.evalWithin input budget (graph.seed input heap)).map
        (fun (word, final) => (word, Buffer.mk final)) :=
  Proofs.run_eq_evalWithin graph input budget heap

theorem returns_iff (graph : Graph args) (input : Tuple (Val cells) args)
    (heap : Heap cells) (word : Word) (final : Heap cells) :
    (∃ fuel, runFuel graph input fuel ⟨heap⟩ = some (word, ⟨final⟩)) ↔
      graph.Returns input heap word final :=
  Proofs.returns_iff graph input heap word final

/-- Absence quantifies over every raw CFG fuel and every native
backedge allowance. -/
theorem no_return_iff (graph : Graph args) (input : Tuple (Val cells) args) (heap : Heap cells) :
    (∀ fuel, runFuel graph input fuel ⟨heap⟩ = none) ↔
      ∀ budget, graph.evalWithin input budget (graph.seed input heap) = none :=
  Proofs.no_return_iff graph input heap

/-- Execution from the emitted entry cannot fail address decoding.
The outer option succeeds at every fuel, including when the inner
return option is absent. -/
theorem cfg_run_isSome (graph : Graph args) (input : Tuple (Val cells) args)
    (fuel : Nat) (initial : Buffer cells) :
    (((lower cells graph).run (evalBody input) fuel .nil).run initial).isSome = true :=
  Proofs.cfg_run_isSome graph input fuel initial

/-- The coloured firing trace and the emitted CFG have the same complete
finite result with independent witnesses. -/
theorem petri_finishes_iff_runFuel (graph : Graph args) (input : Tuple (Val cells) args)
    (heap : Heap cells) (word : Word) (final : Heap cells) :
    Finishes (thetaRuntime cells) (Petri.lower graph) (encodeInput heap input) (encodeResult word final) ↔
      ∃ fuel, runFuel graph input fuel ⟨heap⟩ = some (word, ⟨final⟩) :=
  (Petri.lower_finishes_iff graph input heap word final).trans (returns_iff graph input heap word final).symm

theorem petri_no_finishes_iff_no_return (graph : Graph args) (input : Tuple (Val cells) args) (heap : Heap cells) :
    (∀ output, ¬ Finishes (thetaRuntime cells) (Petri.lower graph) (encodeInput heap input) output) ↔
      ∀ fuel, runFuel graph input fuel ⟨heap⟩ = none :=
  (Petri.no_finishes_iff graph input heap).trans (no_return_iff graph input heap).symm

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.MemRef
