module

public import Silmaril.SSA.MLIR.Signature.FixedSorts.Thms
public import Silmaril.SSA.MLIR.Institution.Arith.Defs

/-! A pure, isolated execute-once example with one explicit block argument. -/

@[expose] public section

namespace Silmaril.MLIR.Institution.Signature.FixedSorts.Examples

open CategoryTheory
open Silmaril.MLIR.Arith (Width)

abbrev core : FixedSorts true Width := ⟨Arith.Op⟩

/-- The fresh label uses the same typed interface as isolated Arith application. -/
inductive Fresh : {a : OpArity true} → Profile a Width → Type where
  | runOnce (arg result : Width) : Fresh (Arith.applyProfile arg result)

abbrev fresh : FixedSorts true Width := ⟨Fresh⟩
abbrev signature : Signature true := toSignature.obj (sum core fresh)

def freshToArith : fresh ⟶ core :=
  ⟨fun | .runOnce a w => .apply a w⟩

/-- Keep old labels and rename the fresh label to the existing scoped application. -/
def mediator : sum core fresh ⟶ core := sum.desc (𝟙 core) freshToArith

def toArith : signature ⟶ Arith.signature := toSignature.map mediator

/-- Evaluate the extension using the existing total Arith model. -/
def model : Model signature := Arith.model.reduct toArith

/-- The first input is deliberately unavailable in the isolated region's scope. -/
abbrev inputs (w : Width) : Fin 2 → Width :=
  Fin.cases ⟨1, by decide⟩ (fun _ => w)

/-- Pass the second input explicitly to the isolated body and yield its doubled value. -/
def scopedDouble (w : Width) : Term signature (inputs w) w :=
  let body : Silmaril.MLIR.Arith.Block [w] w :=
    .letOp (.binary .addi .here .here) (.yield .here)
  Term.app (S := signature) (Γ := inputs w) (p := Arith.applyProfile w w)
    ((sum.inr core fresh).symbol (.runOnce w w))
    (fun _ => .var 1)
    (fun _ _ => (Arith.blockTerm Arith.regionVar body).map (toSignature.map (sum.inl core fresh))) 0

end Silmaril.MLIR.Institution.Signature.FixedSorts.Examples
