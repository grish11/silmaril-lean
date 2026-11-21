module

public import Silmaril.Wasm.Profiles.ISA.Defs
public import Silmaril.Wasm.Models.Syntax.Thms
import Silmaril.Proofs.Wasm.Profiles.ISA

public section

namespace Silmaril.Wasm.Profiles.ISA

open Validation Models

@[simp] theorem Flat.lookup?_opcode (tag : Flat) : lookup? tag.opcode = some tag :=
  Proofs.Wasm.Profiles.ISA.lookup_opcode tag

theorem Flat.lookup?_some {opcode : Opcode} {tag : Flat} : lookup? opcode = some tag ↔ tag.opcode = opcode :=
  Proofs.Wasm.Profiles.ISA.lookup_some

@[simp] theorem Flat.At.toFlat_toOp {inputs outputs} (tag : Flat.At inputs outputs) : tag.toOp.toFlat = tag := by
  cases tag with | exact tag => cases tag <;> rfl

@[simp] theorem Op.toOp_toFlat {inputs outputs} (op : Op inputs outputs) : op.toFlat.toOp = op :=
  (Proofs.Wasm.Profiles.ISA.roundtrips op).1

def Flat.At.equiv (inputs outputs : List CValType) : Flat.At inputs outputs ≃ Op inputs outputs where
  toFun := Flat.At.toOp
  invFun := Op.toFlat
  left_inv := Flat.At.toFlat_toOp
  right_inv := Op.toOp_toFlat

def Flat.equiv : Flat ≃ SomeOp where
  toFun := Flat.pack
  invFun term := term.2.2.tag
  left_inv := by intro tag; cases tag <;> rfl
  right_inv := fun ⟨_, _, op⟩ => (Proofs.Wasm.Profiles.ISA.roundtrips op).2

def RawOp.equiv : RawOp ≃ SomeOp where
  toFun := RawOp.infer
  invFun term := term.2.2.forget
  left_inv := by intro op; cases op <;> rfl
  right_inv := by intro ⟨_, _, op⟩; cases op <;> rfl

def Flat.factoredEquiv : Flat ≃ RawOp := Flat.equiv.trans RawOp.equiv.symm

@[simp] theorem Flat.factoredEquiv_erase (tag : Flat) : (factoredEquiv tag).erase = tag.erase :=
  congrArg (fun term : SomeOp => term.2.2.erase) (RawOp.equiv.apply_symm_apply tag.pack)

theorem Op.sound (ctx : Context) {inputs outputs} (op : Op inputs outputs) :
    InstrOk ctx op.erase (.plain inputs outputs) := Proofs.Wasm.Profiles.ISA.sound ctx op

theorem Flat.sound (ctx : Context) (tag : Flat) : InstrOk ctx tag.erase (.plain tag.inputs tag.outputs) :=
  tag.typed.sound ctx

theorem Admitted.lookup?_some {W : Type} [HasFeatures W] {opcode : Opcode} {op : Admitted W} :
    lookup? W opcode = some op ↔ op.val.opcode = opcode :=
  Proofs.Wasm.Profiles.ISA.admitted_lookup_some

def Admitted.ofLE {W U : Type} [HasFeatures W] [HasFeatures U] (sub : HasFeatures.features W ≤ HasFeatures.features U) :
    Admitted W ↪ Admitted U where
  toFun op := ⟨op.val, inFeatB_mono sub op.val.erase op.property⟩
  inj' := fun _ _ eq => Subtype.ext (congrArg (fun op : Admitted U => op.val) eq)

def Admitted.wasm1To2 : Admitted Wasm1 ↪ Admitted Wasm2 := ofLE v10_le_v20
def Admitted.wasm2To3 : Admitted Wasm2 ↪ Admitted Wasm3 := ofLE v20_le_v30

end Silmaril.Wasm.Profiles.ISA
