module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Join.Finite.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Correctness

/-! # Source occurrences, simultaneous latching, and native finite returns -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond

open SeaOfNodes.Diamond (Model Ty Val ValueSort dataPorts sortValue)
open RVSDG (Dialect PortType Tuple Locals Wires extend)
open RVSDG.NestedTheta (Term iterate)
open Join (Block Opcode model)
open Join.Finite (Plan Stage Table)
open Blocks (Bank)

universe u v w

section Prefix

variable {V S : Type u} {Φ : Dialect.{u, v} V S}
variable {args bank outs : List (PortType V S)} {past frontSigs suffix : List (List (PortType V S))}

/-- Evaluate an emitted base prefix with a continuation determined by
the values of its actual result wires. -/
theorem thenBase_eval (m : RVSDG.Model.{u, v, w} Φ) (fuel : Nat)
    (t : RVSDG.Term Φ args past frontSigs bank)
    (next : Wires args (extend past frontSigs) bank → Term Φ args (extend past frontSigs) suffix outs)
    (entry : Tuple m.Val args) (locals : Locals m.Val past)
    (observe : Tuple m.Val bank → Option (Tuple m.Val outs))
    (agrees : ∀ wires locals', (next wires).eval m fuel entry locals' = observe (wires.read entry locals')) :
    (thenBase t next).eval m fuel entry locals = observe (t.eval m entry locals) :=
  Proofs.thenBase_eval m fuel t next entry locals observe agrees

end Prefix

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable (p : Program src entry) (m : Model.{u, v, w} Op)

/-- Each γ child uses the ordered quads of its checked original arm. -/
theorem Program.arm_body (occurrence : Fin 2) :
    p.stage.table.get occurrence = (p.armPath occurrence).quads :=
  Proofs.arm_body p occurrence

/-- The γ tag preserves which occurrence the source conditional selects. -/
theorem Program.selected_predecessor (bank : Bank (regs := regs) m) :
    p.predecessor (p.stage.choice.eval bank) =
      (if (bank.get p.condition).down then p.trueArm.predecessor p.header
        else p.falseArm.predecessor p.header) :=
  Proofs.selected_predecessor p m bank

/-- The actual γ merge produces all reaching values from the selected
occurrence. No value from the unselected predecessor enters this bank. -/
theorem Program.merge_run (bank : Bank (regs := regs) m) :
    p.plan.lower.run (model m) bank =
      (p.armPath (p.stage.choice.eval bank)).quads.eval m bank := by
  rw [Plan.lower_run]
  exact congrArg (fun block : Block Op regs => block.eval m bank) (p.arm_body _)

theorem Program.afterHeader_eval {args results : List (Ty Data)} {past suffix : List (List (Ty Data))}
    (current : Wires args past (dataPorts regs))
    (finish : Wires args (extend (extend past p.plan.producers) p.tail.producers) (dataPorts regs) →
      Term (Opcode Op) args (extend (extend past p.plan.producers) p.tail.producers) suffix results)
    (fuel : Nat) (input : Tuple (Val m.value) args) (locals : Locals (Val m.value) past)
    (observe : Bank (regs := regs) m → Option (Tuple (Val m.value) results))
    (agrees : ∀ wires locals', (finish wires).eval (model m) fuel input locals' =
      observe (wires.read input locals')) :
    (p.afterHeader current finish).eval (model m) fuel input locals =
      observe (p.tail.eval m (p.stage.eval m (current.read input locals))) :=
  Proofs.afterHeader_eval p m current finish fuel input locals observe agrees

theorem Program.latch_model (bank : Bank (regs := regs) m) :
    (model m).run (.route (.test p.again (.take 1) (.take 0))) bank =
      RVSDG.Theta.bodyResult (model m) (bank.get p.again).down bank :=
  Proofs.latch_model p m bank

theorem routeLatchWith_eval {args : List (Ty Data)} {past : List (List (Ty Data))}
    (again : RVSDG.Port (dataPorts regs) (.value .predicate)) (wires : Wires args past (dataPorts regs))
    (fuel : Nat) (input : Tuple (Val m.value) args) (locals : Locals (Val m.value) past) :
    (routeLatchWith again wires).eval (model m) fuel input locals =
      some (RVSDG.Theta.bodyResult (model m) ((wires.read input locals).get again).down
        (wires.read input locals)) :=
  Proofs.routeLatchWith_eval m again wires fuel input locals

theorem iterateThenReturnWith_eval {past sigs : List (List (Ty Data))}
    (body : Term (Opcode Op) (dataPorts regs) [] sigs (bodyPorts regs))
    (result : RVSDG.Port (dataPorts regs) (.value out)) (wires : Wires (dataPorts regs) past (dataPorts regs))
    (fuel : Nat) (input : Bank (regs := regs) m) (locals : Locals (Val m.value) past) :
    (iterateThenReturnWith body result wires).eval (model m) fuel input locals =
      (iterate (body.run (model m) fuel) (fun tag => tag.down.val == 1) fuel (wires.read input locals)).map
        (fun bank => .cons (bank.get result) .nil) :=
  Proofs.iterateThenReturnWith_eval m body result wires fuel input locals

/-- After the merge and latch, θ sees the exact updated bank and source test. -/
theorem Program.activation_run (fuel : Nat) (old : Bank (regs := regs) m) :
    p.thetaBody.run (model m) fuel old =
      some (RVSDG.Theta.bodyResult (model m) ((p.nextBank m old).get p.again).down (p.nextBank m old)) :=
  Proofs.body_run p m fuel old

theorem Program.lower_iterate (fuel : Nat) (input : Bank (regs := regs) m) :
    p.lower.run (model m) fuel input =
      (iterate (p.thetaBody.run (model m) fuel) (fun tag => tag.down.val == 1)
        fuel ((src entry).body.eval m input)).map (fun bank => .cons (bank.get p.result) .nil) :=
  Proofs.lower_iterate p m fuel input

/-- Match a native budget with one entry visit and the sum of the selected
activation costs, even if the bounded native run exhausts. -/
theorem Program.lower_run (fuel : Nat) (input : Bank (regs := regs) m) :
    p.lower.run (model m) fuel input =
      (src.runFrom m (p.sourceVisits m fuel input) entry input).map (fun value => .cons value .nil) :=
  Proofs.lower_run p m fuel input

/-- A returning native trace gives the minimum source fuel for that return.
Every smaller source budget exhausts. -/
theorem Program.run_at (fuel sourceFuel : Nat) (input : Bank (regs := regs) m)
    (result : sortValue m.value out)
    (returned : p.lower.run (model m) fuel input = some (.cons result .nil)) :
    src.runFrom m sourceFuel entry input =
      if p.sourceVisits m fuel input ≤ sourceFuel then some result else none :=
  Proofs.run_at p m fuel sourceFuel input result returned

/-- A bounded source return has a native return whose selected trace fits
the source budget, and conversely. -/
theorem Program.source_bounded_iff (fuel : Nat) (input : Bank (regs := regs) m)
    (result : sortValue m.value out) :
    src.runFrom m fuel entry input = some result ↔
      ∃ activations, p.lower.run (model m) activations input = some (.cons result .nil) ∧
        p.sourceVisits m activations input ≤ fuel :=
  Proofs.source_bounded_iff p m fuel input result

theorem Program.returns_iff (input : Bank (regs := regs) m) (result : sortValue m.value out) :
    p.lower.Returns (model m) input (.cons result .nil) ↔
      ∃ fuel, src.runFrom m fuel entry input = some result :=
  Proofs.returns_iff p m input result

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond
