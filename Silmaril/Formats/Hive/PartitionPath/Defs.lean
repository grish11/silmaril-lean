module

public import Init.Data.String
public import Init.Data.List.SplitOn

/-!
# Hive partition directory paths

This profile takes a relative directory string. Slash delimits segments and
the first literal equals sign in a segment delimits its key. Each component
is then percent-decoded exactly once as UTF-8. Keys are case sensitive.
Empty input denotes the dataset root.

Rendering emits only URI-unreserved bytes and uppercase escapes inside
components. The null marker is compared after decoding, so any spelling of
that marker denotes null. A literal value equal to the marker is rejected on
render. Empty text remains distinct from null.
-/

@[expose] public section

namespace Silmaril.Formats.Hive.PartitionPath

/-- Each entry has a decoded key and either null or decoded text. -/
abbrev Entry := String × Option String

abbrev Partition := List Entry

structure Options where
  nullMarker : String := "__HIVE_DEFAULT_PARTITION__"
  requiredKeys : List String := []
  deriving Repr

inductive Error where
  | emptyNullMarker
  | emptySegment
  | missingEquals (segment : String)
  | invalidEscape
  | invalidUtf8
  | emptyKey
  | duplicateKey (key : String)
  | missingKey (key : String)
  | nullMarkerCollision (key : String)
  | directoryByteLimit (maximum actual : Nat)
  | segmentArity (expected actual : Nat)
  | filenameByteLimit (maximum actual : Nat)
  | missingFilenameSuffix
  | unsafeFilenameSuffix
  | filenameKeyOrder
  | filenameNull (key : String)
  | unsafeLiteralFilenameValue (key : String)
  deriving BEq, Repr

/-- The outer option distinguishes a missing key from a present null value. -/
def lookup (key : String) (entries : Partition) : Option (Option String) :=
  (entries.find? fun entry => entry.1 == key).map Prod.snd

namespace Percent

def unreserved (b : UInt8) : Bool :=
  let n := b.toNat
  decide ((65 ≤ n ∧ n ≤ 90) ∨ (97 ≤ n ∧ n ≤ 122) ∨ (48 ≤ n ∧ n ≤ 57) ∨
    n = 45 ∨ n = 46 ∨ n = 95 ∨ n = 126)

def hexDigit (n : Nat) : UInt8 :=
  UInt8.ofNat (if n < 10 then 48 + n else 55 + n)

def hexValue (b : UInt8) : Option Nat :=
  let n := b.toNat
  if 48 ≤ n ∧ n ≤ 57 then some (n - 48)
  else if 65 ≤ n ∧ n ≤ 70 then some (n - 55)
  else if 97 ≤ n ∧ n ≤ 102 then some (n - 87)
  else none

def escapeByteWith (escapeUnderscore : Bool) (b : UInt8) : List UInt8 :=
  if unreserved b && !(escapeUnderscore && b == 95) then [b]
  else [37, hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

def escapeWith (escapeUnderscore : Bool) (bytes : List UInt8) : List UInt8 :=
  bytes.flatMap (escapeByteWith escapeUnderscore)

def escapeByte (b : UInt8) : List UInt8 := escapeByteWith false b

def escape (bytes : List UInt8) : List UInt8 := escapeWith false bytes

def unescapeRev : List UInt8 → List UInt8 → Except Error (List UInt8)
  | [], acc => .ok acc.reverse
  | b :: rest, acc =>
    if b == 37 then
      match rest with
      | hi :: lo :: tail =>
        match hexValue hi, hexValue lo with
        | some h, some l => unescapeRev tail (UInt8.ofNat (16 * h + l) :: acc)
        | _, _ => .error .invalidEscape
      | _ => .error .invalidEscape
    else
      unescapeRev rest (b :: acc)

def unescape (bytes : List UInt8) : Except Error (List UInt8) :=
  unescapeRev bytes []

def encodeWith (escapeUnderscore : Bool) (value : String) : String :=
  String.ofList ((escapeWith escapeUnderscore value.toUTF8.data.toList).map (fun b => Char.ofNat b.toNat))

def encode (value : String) : String := encodeWith false value

def decode (value : String) : Except Error String := do
  let bytes ← unescape value.toUTF8.data.toList
  match String.fromUTF8? ⟨bytes.toArray⟩ with
  | some text => return text
  | none => throw .invalidUtf8

end Percent

def parseSegment (options : Options) (segment : String) : Except Error Entry := do
  if segment.isEmpty then throw .emptySegment
  let (rawKey, suffix) := segment.toList.span (· != '=')
  let '=' :: rawValue := suffix | throw (.missingEquals segment)
  let key ← Percent.decode (String.ofList rawKey)
  if key.isEmpty then throw .emptyKey
  let value ← Percent.decode (String.ofList rawValue)
  return (key, if value == options.nullMarker then none else some value)

/-- Reject a repeated decoded key, including identical repeated entries. -/
def validateKeys : List String → Except Error Unit
  | [] => .ok ()
  | key :: tail =>
    if key.isEmpty then .error .emptyKey
    else if tail.contains key then .error (.duplicateKey key)
    else validateKeys tail

def validate (options : Options) (entries : Partition) : Except Error Unit := do
  let keys := entries.map Prod.fst
  validateKeys keys
  match options.requiredKeys.find? (fun key => !keys.contains key) with
  | some key => .error (.missingKey key)
  | none => .ok ()

/-- Parse relative directories, preserving order. Every segment must be a
partition assignment. Missing keys are allowed except those listed in
`requiredKeys`. Additional keys are retained. -/
def parse (options : Options) (path : String) : Except Error Partition :=
  if options.nullMarker.isEmpty then .error .emptyNullMarker
  else
    let parsed := if path.isEmpty then Except.ok [] else (path.splitOn "/").mapM (parseSegment options)
    parsed.bind fun entries => do
      validate options entries
      return entries

def renderSegment (options : Options) (entry : Entry) : Except Error String := do
  let (key, value) := entry
  if value == some options.nullMarker then throw (.nullMarkerCollision key)
  return Percent.encode key ++ "=" ++ Percent.encode (value.getD options.nullMarker)

/-- Render the entries in the supplied order after applying the same key
policy as the parser. Null is emitted using the configured marker. -/
def render (options : Options) (entries : Partition) : Except Error String := do
  if options.nullMarker.isEmpty then throw .emptyNullMarker
  validate options entries
  return String.intercalate "/" (← entries.mapM (renderSegment options))

end Silmaril.Formats.Hive.PartitionPath
