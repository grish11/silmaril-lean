module

public import Init

/-! # Exact Python text

Python strings retain Unicode code points, including surrogate code points.
This value carries contents. Operations that observe object identity need
a separate representation.
-/

@[expose] public section
namespace Silmaril.Languages.Python.Core

structure Text where
  points : List UInt32
  valid : points.all (fun point => point.toNat < 0x110000) = true
  deriving DecidableEq, Repr

def Text.ofPoints? (points : List UInt32) : Option Text :=
  if valid : points.all (fun point => point.toNat < 0x110000) = true then
    some ⟨points, valid⟩
  else none

def Text.ofString (value : String) : Text :=
  ⟨value.toList.map Char.val, by
    simp only [List.all_map, List.all_eq_true, Function.comp_apply, decide_eq_true_eq]
    exact fun char _ => char.valid.elim (fun small => Nat.lt_trans small (by decide)) And.right⟩

def Text.truth (value : Text) : Bool := !value.points.isEmpty

/-- One exact text value per Python code point, in source order. -/
def Text.singletons (value : Text) : List Text :=
  value.points.attach.map fun point =>
    ⟨[point.val], by
      simpa using List.all_eq_true.mp value.valid point.val point.property⟩

/-- CPython 3.13 accepts at least 640 digits under every valid enabled
integer-string conversion limit. Test the magnitude before rendering. -/
def Text.decimal? (value : Int) : Option Text :=
  if value.natAbs < 10 ^ 640 then some (ofString (toString value)) else none

end Silmaril.Languages.Python.Core
