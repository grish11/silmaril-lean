module

public import Silmaril.Formats.JsonBytes.Decide.Defs
public import Silmaril.Semantics.StreamBounds.Defs

/-!
# JSON texts of bounded nesting depth

RFC 8259 §9 lets a parser "set limits on the maximum depth of nesting". This module defines
the depth-bounded sublanguages `languageAt p d` of `JsonBytes.language p`. They are the bound
languages to use for completeness relative to a resource bound (`Silmaril.Acceptor.CompleteFoldOn`
with `B = languageAt p d`, or `Silmaril.Accept.DecidesOn`).

## Depth semantics

Depth is a property of the JSON *value*, read off the grammar, not of the bytes:

* a scalar (`false`, `null`, `true`, a number, a string) has depth `0`;
* an array or object has depth `1 +` the largest depth of its elements or member values, and
  `[]` and `{}` have depth `1`.

So `1` has depth 0, `[]` depth 1, `[[1],{"a":[]}]` depth 3. Brackets inside strings do not count:
`"[[["` has depth 0. This differs from the generic byte-level bracket depth
`Silmaril.Streams.depth` over bytes (which counts every `[`), see `Thms`. Object names are
strings and add nothing. Whitespace is irrelevant.

`ValueAt p d w` says that `w` is a value with *some* derivation of depth at most `d`. The
grammar is ambiguous only in where whitespace goes, which does not change depth, so this is
the depth of the value. The predicates are the grammar of `JsonBytes.Defs` with a depth index.
`Decide.textAtB` decides them (`Thms`).
-/

@[expose] public section

namespace Silmaril.Formats.JsonBytes

open RegularExpression

mutual

/-- A value whose nesting depth is at most the index. -/
inductive ValueAt (p : Profile) : Nat → List UInt8 → Prop
  | scalar {d w} : w ∈ (scalar p).matches' → ValueAt p d w
  | emptyArray {d a b} : a ∈ beginArray.matches' → b ∈ endArray.matches' →
      ValueAt p (d + 1) (a ++ b)
  | array {d a xs b} : a ∈ beginArray.matches' → ElementsAt p d xs → b ∈ endArray.matches' →
      ValueAt p (d + 1) (a ++ xs ++ b)
  | emptyObject {d a b} : a ∈ beginObject.matches' → b ∈ endObject.matches' →
      ValueAt p (d + 1) (a ++ b)
  | object {d a ms b} : a ∈ beginObject.matches' → MembersAt p d ms → b ∈ endObject.matches' →
      ValueAt p (d + 1) (a ++ ms ++ b)

/-- Array elements, each of depth at most the index. -/
inductive ElementsAt (p : Profile) : Nat → List UInt8 → Prop
  | one {d v} : ValueAt p d v → ElementsAt p d v
  | cons {d v s vs} : ValueAt p d v → s ∈ valueSeparator.matches' → ElementsAt p d vs →
      ElementsAt p d (v ++ s ++ vs)

/-- Object members, each value of depth at most the index. -/
inductive MembersAt (p : Profile) : Nat → List UInt8 → Prop
  | one {d k c v} : k ∈ (string p).matches' → c ∈ nameSeparator.matches' → ValueAt p d v →
      MembersAt p d (k ++ c ++ v)
  | cons {d k c v s ms} : k ∈ (string p).matches' → c ∈ nameSeparator.matches' → ValueAt p d v →
      s ∈ valueSeparator.matches' → MembersAt p d ms → MembersAt p d (k ++ c ++ v ++ s ++ ms)

end

/-- A JSON text whose value has nesting depth at most `d`. -/
def TextAt (p : Profile) (d : Nat) (w : List UInt8) : Prop :=
  ∃ a v b, a ∈ ws.matches' ∧ ValueAt p d v ∧ b ∈ ws.matches' ∧ w = a ++ v ++ b

/-- The JSON texts of nesting depth at most `d`. -/
def languageAt (p : Profile) (d : Nat) : Language UInt8 := {w | TextAt p d w}

/-- The naive byte classification `[ {` opening, `] }` closing, for the generic
`Silmaril.Streams.depth`. It ignores strings, so it is *not* JSON depth (`Thms`). -/
def byteBracket (b : UInt8) : Silmaril.Streams.BracketKind :=
  if b = 0x5B ∨ b = 0x7B then .opening else if b = 0x5D ∨ b = 0x7D then .closing else .neutral

namespace Decide

mutual

/-- `ValueAt p d w`, with fuel. -/
def valueAtB (p : Profile) : Nat → Nat → List UInt8 → Bool
  | 0, _, _ => false
  | _ + 1, 0, w => (scalar p).rmatch w
  | n + 1, d + 1, w => (scalar p).rmatch w ||
      (splits w).any fun ar =>
        (beginArray.rmatch ar.1 && (splits ar.2).any fun mb =>
          endArray.rmatch mb.2 && (mb.1.isEmpty || elementsAtB p n d mb.1)) ||
        (beginObject.rmatch ar.1 && (splits ar.2).any fun mb =>
          endObject.rmatch mb.2 && (mb.1.isEmpty || membersAtB p n d mb.1))

/-- `ElementsAt p d w`, with fuel. -/
def elementsAtB (p : Profile) : Nat → Nat → List UInt8 → Bool
  | 0, _, _ => false
  | n + 1, d, w => valueAtB p n d w ||
      (splits w).any fun vr => valueAtB p n d vr.1 && (splits vr.2).any fun sx =>
        valueSeparator.rmatch sx.1 && elementsAtB p n d sx.2

/-- `MembersAt p d w`, with fuel. -/
def membersAtB (p : Profile) : Nat → Nat → List UInt8 → Bool
  | 0, _, _ => false
  | n + 1, d, w =>
      (splits w).any fun mr =>
        ((splits mr.1).any fun kr => (string p).rmatch kr.1 && (splits kr.2).any fun cv =>
          nameSeparator.rmatch cv.1 && valueAtB p n d cv.2) &&
        (mr.2.isEmpty || (splits mr.2).any fun sm =>
          valueSeparator.rmatch sm.1 && membersAtB p n d sm.2)

end

/-- `TextAt p d w`. -/
def textAtB (p : Profile) (d : Nat) (w : List UInt8) : Bool :=
  (splits w).any fun ar => ws.rmatch ar.1 && (splits ar.2).any fun vb =>
    ws.rmatch vb.2 && valueAtB p (2 * vb.1.length + 1) d vb.1

end Decide

end Silmaril.Formats.JsonBytes

end
