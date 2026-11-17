module

public import Silmaril.Cerberus.TV.Profile.Defs
public import Silmaril.Cerberus.TV.Behaviour.Defs
public import Silmaril.Cerberus.Codec.File.Defs

/-!
# Which types a program's executed Core names, and the per-type profile check

A Core→Core statement (`TV.Refines`) is about the port's semantics. A target profile's per-type
check (`Profile.CoherentAt`) is a **necessary filter**, not a transfer: this module computes, per
program, the types named by the Core the dynamics can run, and requires coherence at each.

**What is scanned** (`mentions b`): the wire encoding (`Codec.encodeFileBindings`, round trip
proved in `Silmaril.Cerberus.Codec`) of

* the program part: its own functions, globals, tag definitions, function information and visible
  objects;
* the **runtime library functions and implementation constants it can reach**
  (`reachableStdlib`, `reachableImpl`): every `stdlib` function whose symbol, and every `impl`
  constant whose name (under `PEimpl`/`Impl`), occurs in the program part or, transitively, in a
  reached function or constant.

`Closed.ofBindings b` runs `b.toFile`, which keeps `stdlib` and `impl`; a runtime function or
constant that nothing reached names cannot be called, so leaving it out loses nothing the
dynamics executes. (Core names runtime functions by symbol and implementation constants by
`PEimpl`/`Impl`; a name built at run time would be missed, and Core has none.)

**How the scan reads types** (over-approximating within what it scans):

* a real floating type names its kind (`RealFloating (Float)` …); a Core floating object type or
  value (`OTy_floating`, `OVfloating`) counts as all three kinds;
* `Wint_t` counts as `wchar_t`;
* exact-width, least, fast and maximum-width integers, enums, `ptraddr_t`, arrays, structs, unions
  and atomics are **outside the coherence table** (`Mention.outside`): the check never passes for
  a program that names one.

**What the scan cannot see**, beside what `Profile.issues` does not compare: operations rather
than types (integer conversions, shifts and division go through runtime functions such as
`conv_int` and `catch_exceptional_condition` and the `impl` constants, whose behaviour is the
port's); allocator addresses; byte-level type punning (only the pointee types written in the
program appear); and the enum registry (`Closed.ofBindings` runs with no enum registrations, which
is harmless only because enums are `outside`).

`Profile.AppliesTo p b` is decidable.
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

/-- The text of an atom child, or of a `$str` node's atom. -/
def atomText : Tree → Option String
  | .atom a => some a
  | .tag "$str" 1 cs => match cs ⟨0, by decide⟩ with
    | .atom a => some a
    | _ => none
  | _ => none

/-- The symbols a tree names: each `Symbol` node's digest and number (Lem's symbol equality). -/
def symbolsTree : Tree → List (String × String)
  | .atom _ => []
  | .tag t n cs =>
      let here := if t == "Symbol" ∧ 2 ≤ n then
          match (if h : 0 < n then atomText (cs ⟨0, h⟩) else none),
                (if h : 1 < n then atomText (cs ⟨1, h⟩) else none) with
          | some d, some k => [(d, k)]
          | _, _ => []
        else []
      here ++ (List.ofFn fun i => symbolsTree (cs i)).flatten

/-- The key of a symbol, as `symbolsTree` reads it. -/
def symKey (s : Sym) : List (String × String) := symbolsTree (Codec.sym.enc s)

/-- The implementation constants a tree names: the root tag under each `PEimpl` or `Impl` node. -/
def implsTree : Tree → List String
  | .atom _ => []
  | .tag t n cs =>
      let here := if (t == "PEimpl" || t == "Impl") then
          match (if h : 0 < n then rootTag (cs ⟨0, h⟩) else none) with
          | some c => [c]
          | none => []
        else []
      here ++ (List.ofFn fun i => implsTree (cs i)).flatten

/-- The key of an implementation constant, as `implsTree` reads it. -/
def implKey (c : ImplementationConstant) : Option String := rootTag (Codec.implementationConstant.enc c)

/-- The symbols and implementation constants reachable from the program part, through the runtime
functions and implementation constants they name (a closure, iterated once per runtime entry). -/
def reachable (b : Codec.FileBindings) : List (String × String) × List String :=
  let seedTree := Codec.encodeFileBindings (programPart b)
  let step (st : List (String × String) × List String) : List (String × String) × List String :=
    let (keys, impls) := st
    let fs := b.stdlib.filter fun e => (symKey e.1).any (keys.contains ·)
    let is := b.impl.filter fun e => (implKey e.1).any (impls.contains ·)
    (keys ++ fs.flatMap (fun e => symbolsTree (Codec.funDecl.enc e.2)) ++
        is.flatMap (fun e => symbolsTree (Codec.implDecl.enc e.2)),
      impls ++ fs.flatMap (fun e => implsTree (Codec.funDecl.enc e.2)) ++
        is.flatMap (fun e => implsTree (Codec.implDecl.enc e.2)))
  (List.range (b.stdlib.length + b.impl.length + 1)).foldl (fun st _ => step st)
    (symbolsTree seedTree, implsTree seedTree)

/-- **The runtime functions the program can reach** (by symbol, transitively). -/
def reachableStdlib (b : Codec.FileBindings) : List (Sym × Core.FunDecl Codec.wireModel Unit Unit) :=
  let keys := (reachable b).1
  b.stdlib.filter fun e => (symKey e.1).any (keys.contains ·)

/-- **The implementation constants the program can reach** (transitively). -/
def reachableImpl (b : Codec.FileBindings) :
    List (ImplementationConstant × Core.ImplDecl Codec.wireModel Unit) :=
  let impls := (reachable b).2
  b.impl.filter fun e => (implKey e.1).any (impls.contains ·)

/-- **The types a program's executed Core names** (module docstring), without repetitions: the
program part, the reachable runtime functions and the reachable implementation constants. -/
def mentions (b : Codec.FileBindings) : List Mention :=
  (mentionsTree (Codec.encodeFileBindings
    { b with stdlib := reachableStdlib b, impl := reachableImpl b })).dedup

/-- Whether the profile is coherent at a mention (never at one outside the table). -/
def Profile.coherentAt (p : Profile) : Mention → Bool
  | .scalar s => (p.issues s).isEmpty
  | .outside _ => false

/-- **The per-type check passes**: every scalar type the executed Core names (`mentions`) is
coherent, and it names nothing outside the coherence table. A necessary filter, not a transfer. -/
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

/-- **Core refinement with the profile's per-type check on both programs**: a Core→Core
refinement (`Refines`) of two closed programs given by their bindings, with the profile's
`Spec.Impl` choices, and `Profile.AppliesTo` on both. It is a statement about the port's Core
semantics filtered by a necessary condition, not a statement about the target. -/
structure RefinesOn (p : Profile) (src tgt : Codec.FileBindings) : Prop where
  refines : Refines p.impl (Closed.ofBindings src) (Closed.ofBindings tgt)
  source : p.AppliesTo src
  target : p.AppliesTo tgt

end Silmaril.Cerberus.TV
