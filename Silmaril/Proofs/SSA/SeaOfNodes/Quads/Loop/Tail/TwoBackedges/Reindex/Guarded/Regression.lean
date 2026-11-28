module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded

open SeaOfNodes.Diamond (Val ValueSort dataPorts)
open SeaOfNodes.Loop.SCCP (BankDecidableEq decideTupleCovers)
open SeaOfNodes.Loop.MLIR.CF (model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.Arith (Width)
open Tail.Diamond.MLIR.CF.Pruned.Reindex (Permutation pull)
open SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example (entry facts looping regs word width)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution
  (Admitted admit Artifacts Backend Entry Sentence comparison targetRoom)
open CategoryTheory (Discrete)

private abbrev movedRegs : List (ValueSort Width) := [.predicate, word, .predicate]
private abbrev movedPorts := dataPorts movedRegs

local instance : BankDecidableEq Word movedPorts where
  atPort i := Fin.cases (motive := fun j => DecidableEq (Val Word movedPorts[j]))
    (inferInstance : DecidableEq (ULift Bool))
    (fun j => Fin.cases (motive := fun k => DecidableEq (Val Word movedPorts[k.succ]))
      (inferInstance : DecidableEq (Word width))
      (fun k => Fin.cases (motive := fun l => DecidableEq (Val Word movedPorts[l.succ.succ]))
        (inferInstance : DecidableEq (ULift Bool)) (fun l => l.elim0) k) j) i

private def swap : Registers regs movedRegs :=
  Permutation.cons (Permutation.swap (T := Silmaril.SSA.SeaOfNodes.Diamond.Ty Width)
    (.value .predicate) (.value word) []) (.value .predicate)

private def assumption := facts (.constant ⟨true⟩)
private def original : Admitted regs width :=
  (admit SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example.program assumption).toOption.get (by rfl)

private def moved : Admitted movedRegs width :=
  (admit (program swap original.source) (push swap original.facts)).toOption.get (by rfl)

private def input (side : Bool) : Entry movedRegs :=
  .cons ⟨true⟩ (.cons (7 : Word width) (.cons ⟨side⟩ .nil))

example : pull swap (input false) = entry true false := rfl
example : moved.source.select = .tail (.tail .head) := rfl
example : moved.source.result = .tail .head := rfl
example : moved.checked.side = true := rfl
example : @decide _ (decideTupleCovers moved.facts (input true)) = true := rfl
example : @decide _ (decideTupleCovers moved.facts (input false)) = false := rfl

private def observe (artifacts : Artifacts movedRegs width) (side : Bool) (cfFuel : Nat) :
    Option Nat × Option Nat :=
  ((artifacts.cf.run evalOp cfFuel (encodeValues (input side))).map (fun env => (env.get .here).toNat),
    (artifacts.numbered.2.run (Join.model model) 1 (input side)).map
      (fun packet => (packet.get .head : Word width).toNat))

#guard
  let artifacts := moved.emit
  (observe artifacts true 6, observe artifacts false 7) =
    ((some 99, some 99), (some 7, some 7))

example (backend : Backend) : backend.Returns (reindex swap original).emit (input true) (99 : Word width) :=
  (backend_returns swap backend original _ _).mpr
    ((backend.returns_iff_source original _ _).mpr ⟨5, rfl⟩)

example : Backend.petri.Returns moved.emit (input false) (7 : Word width) :=
  (Backend.petri.returns_iff_source moved _ _).mpr ⟨5, rfl⟩

private def noReturn : Admitted regs width := (admit looping assumption).toOption.get (by rfl)

example (backend : Backend) :
    (targetRoom movedRegs width backend).Sat (Discrete.mk (input false))
      ((comparison backend).sen ((sourceCorridor swap).sen (.terminates original))) :=
  (backend_satisfaction swap backend _ _).mpr (((comparison backend).sat _ _).mpr
    (Part.dom_iff_mem.mpr ⟨(7 : Word width), (original.mem_observe_iff _ _).mpr ⟨5, rfl⟩⟩))

example (backend : Backend) :
    (targetRoom movedRegs width backend).Sat (Discrete.mk (input true))
        ((comparison backend).sen ((sourceCorridor swap).sen (.equation original noReturn))) ↔
      (targetRoom regs width backend).Sat (Discrete.mk (entry true true))
        ((comparison backend).sen (.equation original noReturn)) :=
  backend_satisfaction swap backend _ _

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded
