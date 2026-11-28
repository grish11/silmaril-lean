module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.TextSlice.Defs
import Silmaril.Languages.Python.Core.Text.Slice.Thms

public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.TextSlice

open Source (Name)

theorem Operand.eval_zero {Value : Type} (lookup : Name → Option Value) (asText : Value → Option Core.Text)
    {atom : Atom} {bounds : Core.SliceBounds} {text : Core.Text}
    (read : atom.eval lookup asText = .ok (some text)) (zero : bounds.step = some 0) :
    Operand.eval lookup asText ⟨atom, some bounds⟩ = .error .zeroStep := by
  simp [Operand.eval, read, bind, Except.bind, Core.Text.slice_zero text bounds zero]
  rfl

theorem Guard.eval_left_error {Value : Type} (lookup : Name → Option Value) (asText : Value → Option Core.Text)
    (guard : Guard) {error : Failure} (failed : guard.left.eval lookup asText = .error error) :
    guard.eval lookup asText = .error error := by
  simp [Guard.eval, failed, bind, Except.bind]

theorem Guard.eval_right_error {Value : Type} (lookup : Name → Option Value) (asText : Value → Option Core.Text)
    (guard : Guard) {left : Option Core.Text} {error : Failure}
    (read : guard.left.eval lookup asText = .ok left) (failed : guard.right.eval lookup asText = .error error) :
    guard.eval lookup asText = .error error := by
  simp [Guard.eval, read, failed, bind, Except.bind]

theorem Guard.eval_equal {Value : Type} (lookup : Name → Option Value) (asText : Value → Option Core.Text)
    (guard : Guard) {left right : Core.Text}
    (first : guard.left.eval lookup asText = .ok (some left)) (second : guard.right.eval lookup asText = .ok (some right))
    (equal : left.points = right.points) :
    guard.eval lookup asText = .ok () := by
  simp [Guard.eval, first, second, equal, bind, Except.bind, pure, Except.pure]

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.TextSlice
