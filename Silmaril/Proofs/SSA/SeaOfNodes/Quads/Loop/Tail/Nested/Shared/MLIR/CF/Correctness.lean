module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.Proofs

open SeaOfNodes.Diamond (ValueSort sortValue)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues valueBits valueWidth)
open Silmaril.MLIR.Arith (Width Env)
open Diamond.MLIR.CF (siteFrame lowerSource_run source_site_eval runBlock_eq_of_frames)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)
variable (input : Bank (regs := regs) model)

private theorem lower_from_site (fuel : Nat) (id : Fin size) (old : Bank (regs := regs) model) :
    (lower p).runFrom evalOp (fuel + 1) (encodeValues input) (siteFrame id old) =
      (src.runFrom model fuel id old).map (fun value => Env.cons (valueBits value) .nil) :=
  runBlock_eq_of_frames (src := src) (lower p) input siteFrame .exit
    (fun id old => source_site_eval input old id) rfl fuel id old _ _ (source_site_eval input old id)

theorem from_header_eq_prefix (fuel : Nat) (old : Bank (regs := regs) model) :
    let occurrence := p.toControl.selected model old
    (lower p).runFrom evalOp (fuel + p.prefixVisits occurrence + 1) (encodeValues input) (siteFrame p.header old) =
      (lower p).runFrom evalOp (fuel + 1) (encodeValues input)
        (siteFrame (p.prefixTarget occurrence) (p.prefixBank model old occurrence)) := by
  dsimp only
  rw [lower_from_site, lower_from_site, p.run_prefix]

theorem from_header_eq_merge (fuel : Nat) (old : Bank (regs := regs) model) :
    let occurrence := p.toControl.selected model old
    (lower p).runFrom evalOp (fuel + p.mergeVisits occurrence + 1) (encodeValues input) (siteFrame p.header old) =
      (lower p).runFrom evalOp (fuel + 1) (encodeValues input)
        (siteFrame p.join (p.mergeBank model old occurrence)) := by
  dsimp only
  rw [lower_from_site, lower_from_site, p.run_to_merge]

theorem returns_iff (bits : Word (valueWidth out)) :
    (∃ cfFuel, (lower p).run evalOp cfFuel (encodeValues input) = some (.cons bits .nil)) ↔
      ∃ (fuel : Nat) (value : sortValue Word out), src.runFrom model fuel entry input = some value ∧ valueBits value = bits := by
  constructor
  · rintro ⟨_ | fuel, returned⟩
    · cases returned
    · rw [lower, lowerSource_run] at returned
      cases source : src.runFrom model fuel entry input with
      | none => simp [source] at returned
      | some value =>
        have same := Option.some.inj ((congrArg (Option.map (fun x => Env.cons (valueBits x) .nil)) source).symm.trans returned)
        exact ⟨fuel, value, source, congrArg (fun env => env.get .here) same⟩
  · rintro ⟨fuel, value, returned, encodes⟩
    exact ⟨fuel + 1, by rw [lower, lowerSource_run, returned, Option.map_some, encodes]⟩

theorem noFiniteReturn_iff :
    (lower p).Diverges evalOp (encodeValues input) ↔ ∀ fuel, src.runFrom model fuel entry input = none := by
  constructor
  · intro absent fuel
    have exhausted := absent (fuel + 1)
    rw [lower, lowerSource_run] at exhausted
    exact Option.map_eq_none_iff.mp exhausted
  · intro absent fuel
    cases fuel with
    | zero => rfl
    | succ fuel => rw [lower, lowerSource_run, absent]; rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.Proofs
