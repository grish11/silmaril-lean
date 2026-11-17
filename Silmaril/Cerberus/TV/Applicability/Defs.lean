module

public import Silmaril.Cerberus.TV.Profile.Defs
public import Silmaril.Cerberus.TV.Behaviour.Defs
public import Silmaril.Cerberus.Codec.File.Defs

/-!
# Which types a program mentions, and whether a profile applies to it

A Core→Core statement (`TV.Refines`) is about the port's semantics. It says something about a
real target only for programs whose types the target profile agrees on (`Profile.CoherentAt`,
per scalar type). This module computes, **per program**, the types its own functions, globals,
tag definitions and function information mention, and requires coherence at each of them.

`mentions b` scans the wire encoding of the program part of `b` (`Codec.encodeFileBindings`
with the runtime library maps `stdlib` and `impl` emptied; the codec's round trip is proved in
`Silmaril.Cerberus.Codec`). It over-approximates:

* a real floating type names its kind (`RealFloating (Float)` …); a Core floating object type or
  value (`OTy_floating`, `OVfloating`), which does not, counts as all three kinds;
* `Wint_t` counts as `wchar_t`;
* exact-width, least, fast and maximum-width integers, enums, `ptraddr_t`, arrays, structs, unions
  and atomics are **outside the coherence table** (`Mention.outside`): nothing compares their
  layout yet, so a profile never applies to a program that mentions one.

`Profile.AppliesTo p b`: every mentioned scalar type is coherent and nothing outside the table is
mentioned. It is decidable. It is necessary, not sufficient, for a Core result about `b` to say
something about the target (`Profile` lists what coherence does not compare).
-/

@[expose] public section

namespace Silmaril.Cerberus.TV

open Silmaril.TaggedCodec (Tree)

/-- A type a program mentions. -/
inductive Mention where
  | scalar (s : Scalar)
  | outside (tag : String)
  deriving DecidableEq, Repr

/-- The mentions of one node, from its tag and its first child's tag. -/
def mentionOf (tag : String) (first : Option String) : List Mention :=
  let floats := [Mention.scalar .float, .scalar .double, .scalar .longDouble]
  match tag, first with
  | "RealFloating", some "Float" => [.scalar .float]
  | "RealFloating", some "Double" => [.scalar .double]
  | "RealFloating", some "LongDouble" => [.scalar .longDouble]
  | "RealFloating", _ => floats
  | "OTy_floating", _ => floats
  | "OVfloating", _ => floats
  | "Signed", some "Ichar" => [.scalar .schar]
  | "Signed", some "Short" => [.scalar .short]
  | "Signed", some "Int_" => [.scalar .int]
  | "Signed", some "Long" => [.scalar .long]
  | "Signed", some "LongLong" => [.scalar .longLong]
  | "Signed", some "Intptr_t" => [.scalar .intptr]
  | "Unsigned", some "Ichar" => [.scalar .uchar]
  | "Unsigned", some "Short" => [.scalar .ushort]
  | "Unsigned", some "Int_" => [.scalar .uint]
  | "Unsigned", some "Long" => [.scalar .ulong]
  | "Unsigned", some "LongLong" => [.scalar .ulongLong]
  | "Unsigned", some "Intptr_t" => [.scalar .uintptr]
  | "Signed", some t => [.outside t]
  | "Unsigned", some t => [.outside t]
  | "Char", _ => [.scalar .char]
  | "Bool", _ => [.scalar .bool]
  | "Wchar_t", _ => [.scalar .wchar]
  | "Wint_t", _ => [.scalar .wchar]
  | "Size_t", _ => [.scalar .size]
  | "Ptrdiff_t", _ => [.scalar .ptrdiff]
  | "Pointer", _ => [.scalar .pointer]
  | "OTy_pointer", _ => [.scalar .pointer]
  | "Enum", _ => [.outside "Enum"]
  | "Ptraddr_t", _ => [.outside "Ptraddr_t"]
  | "Array", _ => [.outside "Array"]
  | "Struct", _ => [.outside "Struct"]
  | "Union", _ => [.outside "Union"]
  | "Atomic", _ => [.outside "Atomic"]
  | "OTy_array", _ => [.outside "Array"]
  | "OTy_struct", _ => [.outside "Struct"]
  | "OTy_union", _ => [.outside "Union"]
  | _, _ => []

/-- The tag of a tree's root, if it is a node. -/
def rootTag : Tree → Option String
  | .atom _ => none
  | .tag t _ _ => some t

/-- Every mention in a tree. -/
def mentionsTree : Tree → List Mention
  | .atom _ => []
  | .tag t n cs =>
      let first := if h : 0 < n then rootTag (cs ⟨0, h⟩) else none
      mentionOf t first ++ (List.ofFn fun i => mentionsTree (cs i)).flatten

/-- The program part of a file: the runtime library maps emptied. -/
def programPart (b : Codec.FileBindings) : Codec.FileBindings :=
  { b with stdlib := [], impl := [] }

/-- **The types a program mentions** (module docstring), without repetitions. -/
def mentions (b : Codec.FileBindings) : List Mention :=
  (mentionsTree (Codec.encodeFileBindings (programPart b))).dedup

/-- Whether the profile is coherent at a mention (never at one outside the table). -/
def Profile.coherentAt (p : Profile) : Mention → Bool
  | .scalar s => (p.issues s).isEmpty
  | .outside _ => false

/-- **A profile applies to a program**: every scalar type it mentions is coherent, and it
mentions nothing outside the coherence table. -/
def Profile.AppliesTo (p : Profile) (b : Codec.FileBindings) : Prop :=
  (mentions b).all p.coherentAt = true

instance (p : Profile) (b : Codec.FileBindings) : Decidable (p.AppliesTo b) :=
  inferInstanceAs (Decidable (_ = true))

/-- The mentions that block applicability, with the reason. -/
def Profile.blockers (p : Profile) (b : Codec.FileBindings) : List (Mention × List Issue) :=
  (mentions b).filterMap fun m => match m with
    | .scalar s => match p.issues s with
      | [] => none
      | is => some (m, is)
    | .outside t => some (m, [.unknown s!"{t}: outside the coherence table"])

/-- A closed program from a file's bindings. -/
def Closed.ofBindings (b : Codec.FileBindings) (args : List String := []) : Closed :=
  ⟨b.toFile, ∅, args⟩

/-- **Refinement on a target profile**: a Core→Core refinement (`Refines`) of two closed programs
given by their bindings, with the profile's implementation-defined choices, where the profile
applies to both. It is still a statement about the port's Core semantics; applicability is
necessary, not sufficient, for it to describe the target. -/
structure RefinesOn (p : Profile) (src tgt : Codec.FileBindings) : Prop where
  refines : Refines p.impl (Closed.ofBindings src) (Closed.ofBindings tgt)
  source : p.AppliesTo src
  target : p.AppliesTo tgt

end Silmaril.Cerberus.TV
