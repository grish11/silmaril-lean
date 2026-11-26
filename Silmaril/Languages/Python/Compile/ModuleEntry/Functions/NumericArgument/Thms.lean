module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.NumericArgument.Defs
import Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.NumericArgument

public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.NumericArgument

theorem testBit_bitwise (operation : Bool → Bool → Bool) (left right : Int) (index : Nat) :
    testBit (bitwise operation left right) index = operation (testBit left index) (testBit right index) :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.NumericArgument.testBit_bitwise operation left right index

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.NumericArgument
