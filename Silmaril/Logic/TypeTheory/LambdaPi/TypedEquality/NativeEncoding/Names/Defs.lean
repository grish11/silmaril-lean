module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.Institution.Thms
public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeSignature.Realization
public import Silmaril.Logic.TypeTheory.LambdaPi.Encoding.Thms

@[expose] public section
namespace Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeEncoding

/-- Canonical globals are strings of x's. Length gives their inverse index. -/
def name (i : ℕ) : String := String.ofList (List.replicate i 'x')

def index (c : String) : Option ℕ := if c = name c.length then some c.length else none

def names (n : ℕ) : Fin n → String := fun i => name i.val

/-- Extend a finite source map to all native constant names. Unused canonical
names shift past the target globals, so composition avoids accidental capture. -/
def image {S T : Institution.Signature} (F : Institution.Map S T) (c : String) : LambdaPi.Term :=
  match index c with
  | none => .constant c
  | some i =>
      if hi : i < S.scope then
        NativeConversion.term (NativeSignature.globals (names T.scope)) (F.terms ⟨i, hi⟩)
      else .constant (name (i - S.scope + T.scope))

end Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeEncoding
