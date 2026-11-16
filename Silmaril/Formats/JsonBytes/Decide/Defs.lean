module

public import Silmaril.Formats.JsonBytes.Defs

/-!
# A decision procedure for the JSON byte language

`textB p w` decides `w ∈ JsonBytes.language p` (`Silmaril.Formats.JsonBytes.Decide.Thms`:
`textB_iff`). It follows the grammar literally: each rule tries every split of its input
into the rule's parts, and checks the lexical parts with Mathlib's `rmatch`. Recursion is
bounded by fuel. Fuel `2 * w.length + 1` suffices for a value, because every structural token,
separator and value is non-empty.

This procedure is a reference oracle, not a parser. It is polynomial but of high degree in the
input length, so it suits small kernel-checked tests (`decide +kernel`), not real inputs. Its
only purpose is to make the language decidable with a proof; readers should be compared with
the language, not with this procedure's running time.
-/

@[expose] public section

namespace Silmaril.Formats.JsonBytes.Decide

open RegularExpression

/-- Every way to cut a list into a prefix and a suffix. -/
def splits {α : Type} : List α → List (List α × List α)
  | [] => [([], [])]
  | x :: xs => ([], x :: xs) :: (splits xs).map fun ab => (x :: ab.1, ab.2)

mutual

/-- `Value p w`, with fuel. -/
def valueB (p : Profile) : Nat → List UInt8 → Bool
  | 0, _ => false
  | n + 1, w => (scalar p).rmatch w ||
      (splits w).any fun ar =>
        (beginArray.rmatch ar.1 && (splits ar.2).any fun mb =>
          endArray.rmatch mb.2 && (mb.1.isEmpty || elementsB p n mb.1)) ||
        (beginObject.rmatch ar.1 && (splits ar.2).any fun mb =>
          endObject.rmatch mb.2 && (mb.1.isEmpty || membersB p n mb.1))

/-- `Elements p w`, with fuel. -/
def elementsB (p : Profile) : Nat → List UInt8 → Bool
  | 0, _ => false
  | n + 1, w => valueB p n w ||
      (splits w).any fun vr => valueB p n vr.1 && (splits vr.2).any fun sx =>
        valueSeparator.rmatch sx.1 && elementsB p n sx.2

/-- `Members p w`, with fuel: a member `k c v`, then nothing or a separator and members. -/
def membersB (p : Profile) : Nat → List UInt8 → Bool
  | 0, _ => false
  | n + 1, w =>
      (splits w).any fun mr =>
        ((splits mr.1).any fun kr => (string p).rmatch kr.1 && (splits kr.2).any fun cv =>
          nameSeparator.rmatch cv.1 && valueB p n cv.2) &&
        (mr.2.isEmpty || (splits mr.2).any fun sm =>
          valueSeparator.rmatch sm.1 && membersB p n sm.2)

end

/-- `Text p w`: whitespace, a value with enough fuel, whitespace. -/
def textB (p : Profile) (w : List UInt8) : Bool :=
  (splits w).any fun ar => ws.rmatch ar.1 && (splits ar.2).any fun vb =>
    ws.rmatch vb.2 && valueB p (2 * vb.1.length + 1) vb.1

end Silmaril.Formats.JsonBytes.Decide

end
