module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Thms

/-! Typed signature boundaries for the admitted five-block SCCP profile. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Institution

open CategoryTheory Silmaril.Logic.Institution
open SeaOfNodes.Diamond (Val ValueSort dataPorts)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)
open Tail.Diamond.MLIR.CF.Pruned.Reindex (Permutation pull)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution
  (Admitted Artifacts Backend Entry Sentence observationRoom sourceRoom)

/-- Executable equality at each fixed-width word or Boolean predicate coordinate. -/
@[instance_reducible]
def decidableBank : (regs : List (ValueSort Width)) → BankDecidableEq Word (dataPorts regs)
  | [] => ⟨fun i => i.elim0⟩
  | sort :: rest =>
    ⟨fun i => Fin.cases (motive := fun j => DecidableEq (Val Word (dataPorts (sort :: rest))[j]))
      (match sort with
       | .predicate => (inferInstance : DecidableEq (ULift Bool))
       | .data w => (inferInstance : DecidableEq (Word w)))
      (decidableBank rest).atPort i⟩

-- The result width and the primitive interpretation stay fixed across each institution.
/-- An ordered typed bank, with its executable equality dictionary for SCCP admission. -/
structure Signature where
  regs : List (ValueSort Width)
  bankEq : BankDecidableEq Word (dataPorts regs) := decidableBank regs

instance : Category Signature where
  Hom S T := Registers S.regs T.regs
  id S := Permutation.refl (dataPorts S.regs)
  comp h k := Permutation.trans h k
  id_comp _ := funext fun _ => Equiv.ext fun _ => rfl
  comp_id _ := funext fun _ => Equiv.ext fun _ => rfl
  assoc _ _ _ := funext fun _ => Equiv.ext fun _ => rfl

abbrev AdmittedAt (S : Signature) (result : Width) :=
  @Admitted S.regs result S.bankEq

abbrev Valuation (S : Signature) := Entry S.regs

variable {S T : Signature} {result : Width}

def mapAdmitted (h : S ⟶ T) (p : AdmittedAt S result) : AdmittedAt T result :=
  @Guarded.reindex S.regs T.regs result S.bankEq T.bankEq h p

/-- Sentences travel forward; valuations are pulled back along the register map. -/
def reduct (h : S ⟶ T) (input : Valuation T) : Valuation S :=
  pull h input

/-- Retain an admitted source for re-emission, alongside the actual generated
artifacts. In particular, the Petri observer uses the stored numbered graph. -/
structure Generated (S : Signature) (result : Width) where
  source : AdmittedAt S result
  artifacts : Artifacts S.regs result
  generated : artifacts = (@Admitted.emit S.regs result S.bankEq source)

def Generated.lower (p : AdmittedAt S result) : Generated S result :=
  ⟨p, @Admitted.emit S.regs result S.bankEq p, rfl⟩

def Generated.map (h : S ⟶ T) (p : Generated S result) : Generated T result :=
  lower (mapAdmitted h p.source)

noncomputable abbrev nativeRoom (result : Width) (S : Signature) : Room.{0, 0, 0} :=
  @sourceRoom S.regs result S.bankEq

/-- Interpret generated sentences using the chosen actual artifact observer. -/
noncomputable def generatedRoom (result : Width) (backend : Backend) (S : Signature) : Room.{0, 0, 0} :=
  observationRoom (fun (p : Generated S result) input => backend.observe p.artifacts input)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Institution
