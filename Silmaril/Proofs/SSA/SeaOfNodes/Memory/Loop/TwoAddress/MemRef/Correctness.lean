module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.MemRef.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.MemRef.Proofs

open RVSDG (Tuple)
open Silmaril.MLIR.Arith (Env)
open Silmaril.MLIR.CF (Frame Edge Terminator)
open Silmaril.MLIR.CF.Ordered (Block runBlock)
open Silmaril.MLIR.MemRef (Buffer)
open Loop.MLIR.MemRef (runActivation lowerActivation_run tailSelector)
open Loop.MLIR.MemRef.CF (resultTypes wordWidth)
open Silmaril.MLIR.Pure (i1)

set_option backward.isDefEq.respectTransparency false

variable {cells : Nat} {args : List ValueSort}

private theorem encodeAddress_toNat (address : Address cells) :
    (encodeAddress address).toNat = address.val := by
  have h : cells ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt address.isLt)
  exact (BitVec.toNat_ofNat _ _).trans (Nat.mod_eq_of_lt
    (address.isLt.trans ((Nat.log2_lt h).mp (Nat.lt_succ_self _))))

theorem decodeAddress_encode (address : Address cells) :
    decodeAddress (encodeAddress address) = some address := by
  simp [decodeAddress, encodeAddress_toNat, address.isLt]

theorem decodeAddress_eq_some (value : BitVec (addressWidth cells).val) (address : Address cells) :
    decodeAddress value = some address ↔ value = encodeAddress address := by
  constructor
  · intro decoded
    unfold decodeAddress at decoded
    split at decoded
    · exact BitVec.eq_of_toNat_eq ((congrArg Fin.val (Option.some.inj decoded)).trans
        (encodeAddress_toNat address).symm)
    · cases decoded
  · rintro rfl
    exact decodeAddress_encode address

theorem decodeAddresses_encode (first second : Address cells) :
    decodeAddresses (encodeAddresses first second) = some (first, second) := by
  simp [decodeAddresses, encodeAddresses, Env.get, decodeAddress_encode]

theorem decodeAddresses_eq_some (env : Env (headerTypes cells)) (first second : Address cells) :
    decodeAddresses env = some (first, second) ↔ env = encodeAddresses first second := by
  constructor
  · intro decoded
    cases env with
    | cons a tail =>
      cases tail with
      | cons b tail =>
        cases tail
        change (decodeAddress (cells := cells) a).bind (fun x =>
          (decodeAddress (cells := cells) b).bind (fun y => some (x, y))) = some (first, second) at decoded
        simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at decoded
        obtain ⟨x, hx, y, hy, rfl, rfl⟩ := decoded
        exact congrArg₂ (fun a b => Env.cons a (Env.cons b Env.nil))
          ((decodeAddress_eq_some a x).mp hx) ((decodeAddress_eq_some b y).mp hy)
  · rintro rfl
    exact decodeAddresses_encode first second

theorem header_rejects (graph : Graph args) (input : Tuple (Val cells) args)
    (env : Env (headerTypes cells)) (buffer : Buffer cells) (invalid : decodeAddresses env = none) :
    (Block.eval (evalBody input) ((lower cells graph).block .header) env).run buffer = none := by
  change ((decodeAddresses env).bind _).bind _ = none
  rw [invalid]
  rfl

private theorem activation_outputs (graph : Graph args) (input : Tuple (Val cells) args)
    (header : Header cells) :
    (evalBody input ((lower cells graph).block .header).body
      (encodeAddresses header.first header.second)).run ⟨header.heap⟩ =
      let operands := header.operands input
      let result := graph.activation.body.denote operands header.heap
      let next := graph.feedback input header result.2
      some (.cons (BitVec.ofBool ((tailSelector.{0} result.1 (graph.activation.stopWord operands)).down != 0))
        (.cons result.1 (encodeAddresses next.first next.second)), ⟨result.2⟩) := by
  change (decodeAddresses (encodeAddresses header.first header.second)).bind _ = _
  rw [decodeAddresses_encode]
  change (let (.cons selector (.cons word .nil), final) :=
      runActivation graph.activation (header.operands input) ⟨header.heap⟩
    some (Env.cons (w := i1) (BitVec.ofBool (selector.down != 0))
      (Env.cons (w := wordWidth) word (encodeAddresses ((header.operands input).get graph.feedbackFirst)
        ((header.operands input).get graph.feedbackSecond))), final)) = _
  rw [lowerActivation_run]
  dsimp [Graph.feedback]
  rfl

theorem header_transition (graph : Graph args) (input : Tuple (Val cells) args) (header : Header cells) :
    (Block.eval (evalBody input) ((lower cells graph).block .header)
      (encodeAddresses header.first header.second)).run ⟨header.heap⟩ =
      some (match graph.step input header with
        | .inl (word, final) => (.inl ⟨Label.exit, .cons word .nil⟩, ⟨final⟩)
        | .inr next => (.inl ⟨Label.header, encodeAddresses next.first next.second⟩, ⟨next.heap⟩)) := by
  let block := (lower cells graph).block .header
  change ((evalBody input block.body (encodeAddresses header.first header.second)).run ⟨header.heap⟩).bind
    (fun (values, final) => some (block.terminator.eval values, final)) = _
  rw [activation_outputs]
  by_cases stop : (graph.activation.body.denote (header.operands input) header.heap).1 =
      graph.activation.stopWord (header.operands input)
  all_goals
    simp [Graph.step, Loop.Graph.step, tailSelector, stop, block, lower, Graph.feedback,
      Terminator.eval, Edge.eval, Silmaril.MLIR.Pure.Operands.eval, Env.get, encodeAddresses]
    first | rfl | exact ⟨rfl, rfl⟩

private def fromHeader (graph : Graph args) (input : Tuple (Val cells) args)
    (fuel : Nat) (header : Header cells) : Option (Word × Buffer cells) := do
  let cfg := lower cells graph
  let (result, final) ← (runBlock cfg.block (Block.eval (evalBody input)) .nil fuel
    (cfg.block .header) (encodeAddresses header.first header.second)).run ⟨header.heap⟩
  result.map fun values => (values.get .here, final)

private theorem fromHeader_succ (graph : Graph args) (input : Tuple (Val cells) args)
    (fuel : Nat) (header : Header cells) :
    fromHeader graph input (fuel + 1) header =
      match graph.step input header with
      | .inl (word, final) => if fuel = 0 then none else some (word, ⟨final⟩)
      | .inr next => fromHeader graph input fuel next := by
  conv_lhs => unfold fromHeader; unfold runBlock
  simp only [StateT.run, Bind.bind, StateT.bind, Pure.pure]
  rw [show Block.eval (evalBody input) ((lower cells graph).block .header)
      (encodeAddresses header.first header.second) ⟨header.heap⟩ = _
    from header_transition graph input header]
  rcases graph.step input header with ⟨word, final⟩ | next
  · cases fuel <;> rfl
  · rfl

private theorem fromHeader_one (graph : Graph args) (input : Tuple (Val cells) args)
    (header : Header cells) : fromHeader graph input 1 header = none := by
  rw [fromHeader_succ]
  rcases graph.step input header with ⟨word, final⟩ | next <;> rfl

private theorem fromHeader_eq (graph : Graph args) (input : Tuple (Val cells) args)
    (budget : Nat) (header : Header cells) :
    fromHeader graph input (budget + 2) header =
      (graph.evalWithin input budget header).map (fun (word, final) => (word, Buffer.mk final)) := by
  induction budget generalizing header with
  | zero =>
    rw [fromHeader_succ, Graph.evalWithin]
    rcases graph.step input header with ⟨word, final⟩ | next
    · rfl
    · exact fromHeader_one graph input next
  | succ budget ih =>
    rw [show budget + 1 + 2 = (budget + 2) + 1 by rfl, fromHeader_succ, Graph.evalWithin]
    rcases graph.step input header with ⟨word, final⟩ | next
    · rfl
    · exact ih next

private theorem runFuel_succ (graph : Graph args) (input : Tuple (Val cells) args)
    (fuel : Nat) (heap : Heap cells) :
    runFuel graph input (fuel + 1) ⟨heap⟩ =
      fromHeader graph input fuel (graph.seed input heap) :=
  rfl

theorem runFuel_eq_of_lt_three (graph : Graph args) (input : Tuple (Val cells) args)
    (fuel : Nat) (heap : Heap cells) (below : fuel < 3) :
    runFuel graph input fuel ⟨heap⟩ = none := by
  have small : fuel = 0 ∨ fuel = 1 ∨ fuel = 2 := by omega
  rcases small with rfl | rfl | rfl
  · rfl
  · rfl
  · exact fromHeader_one graph input (graph.seed input heap)

theorem run_eq_evalWithin (graph : Graph args) (input : Tuple (Val cells) args)
    (budget : Nat) (heap : Heap cells) :
    run graph input budget ⟨heap⟩ =
      (graph.evalWithin input budget (graph.seed input heap)).map
        (fun (word, final) => (word, Buffer.mk final)) :=
  (runFuel_succ graph input (budget + 2) heap).trans (fromHeader_eq graph input budget (graph.seed input heap))

private theorem run_success_iff (graph : Graph args) (input : Tuple (Val cells) args)
    (budget : Nat) (heap : Heap cells) (word : Word) (final : Heap cells) :
    run graph input budget ⟨heap⟩ = some (word, ⟨final⟩) ↔
      graph.evalWithin input budget (graph.seed input heap) = some (word, final) := by
  rw [run_eq_evalWithin]
  rcases graph.evalWithin input budget (graph.seed input heap) with _ | ⟨value, state⟩ <;> simp

theorem returns_iff (graph : Graph args) (input : Tuple (Val cells) args)
    (heap : Heap cells) (word : Word) (final : Heap cells) :
    (∃ fuel, runFuel graph input fuel ⟨heap⟩ = some (word, ⟨final⟩)) ↔
      graph.Returns input heap word final := by
  constructor
  · rintro ⟨fuel, observed⟩
    by_cases enough : 3 ≤ fuel
    · obtain ⟨budget, rfl⟩ := Nat.exists_eq_add_of_le enough
      rw [Nat.add_comm 3 budget] at observed
      exact ⟨budget, (run_success_iff graph input budget heap word final).mp observed⟩
    · rw [runFuel_eq_of_lt_three graph input fuel heap (by omega)] at observed
      cases observed
  · rintro ⟨budget, observed⟩
    exact ⟨budget + 3, (run_success_iff graph input budget heap word final).mpr observed⟩

theorem no_return_iff (graph : Graph args) (input : Tuple (Val cells) args) (heap : Heap cells) :
    (∀ fuel, runFuel graph input fuel ⟨heap⟩ = none) ↔
      ∀ budget, graph.evalWithin input budget (graph.seed input heap) = none := by
  constructor
  · intro missing budget
    have absent := missing (budget + 3)
    change run graph input budget ⟨heap⟩ = none at absent
    rw [run_eq_evalWithin] at absent
    rcases evaluated : graph.evalWithin input budget (graph.seed input heap) with _ | result
    · rfl
    · simp [evaluated] at absent
  · intro missing fuel
    by_cases enough : 3 ≤ fuel
    · obtain ⟨budget, rfl⟩ := Nat.exists_eq_add_of_le enough
      rw [Nat.add_comm 3 budget]
      change run graph input budget ⟨heap⟩ = none
      rw [run_eq_evalWithin, missing]
      rfl
    · exact runFuel_eq_of_lt_three graph input fuel heap (by omega)

private theorem fromHeader_run_isSome (graph : Graph args) (input : Tuple (Val cells) args)
    (fuel : Nat) (header : Header cells) :
    let cfg := lower cells graph
    ((runBlock cfg.block (Block.eval (evalBody input)) .nil fuel (cfg.block .header)
      (encodeAddresses header.first header.second)).run ⟨header.heap⟩).isSome = true := by
  induction fuel generalizing header with
  | zero => rfl
  | succ fuel ih =>
    dsimp only
    conv_lhs => unfold runBlock
    simp only [StateT.run, Bind.bind, StateT.bind, Pure.pure]
    rw [show Block.eval (evalBody input) ((lower cells graph).block .header)
      (encodeAddresses header.first header.second) ⟨header.heap⟩ = _
      from header_transition graph input header]
    rcases graph.step input header with ⟨word, final⟩ | next
    · cases fuel <;> rfl
    · exact ih next

theorem cfg_run_isSome (graph : Graph args) (input : Tuple (Val cells) args)
    (fuel : Nat) (initial : Buffer cells) :
    (((lower cells graph).run (evalBody input) fuel .nil).run initial).isSome = true := by
  cases initial with
  | mk heap =>
    cases fuel with
    | zero => rfl
    | succ fuel => exact fromHeader_run_isSome graph input fuel (graph.seed input heap)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.MemRef.Proofs
