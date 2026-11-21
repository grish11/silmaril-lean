module

public import Silmaril.Formats.Cbor.Drisl.Defs
public import Silmaril.Encoding.Base32

@[expose] public section

namespace Silmaril.Formats.Cbor.Drisl

/-- `any` permits canonical CIDv1 with any codec and multihash numbers, not
arbitrary bytes or legacy CIDv0. It does not consult the multicodec registry. -/
inductive CidProfile where
  | any | dasl | bdasl
  deriving DecidableEq, Repr

/-- Read one shortest unsigned multiformats varint, capped at nine bytes. -/
def cidVarint? : Nat → List UInt8 → Option (Nat × List UInt8)
  | fuel + 1, byte :: tail => do
    if byte.toNat < 128 then
      pure (byte.toNat, tail)
    else
      let (more, rest) ← cidVarint? fuel tail
      if more = 0 then none else some (byte.toNat % 128 + 128 * more, rest)
  | _, _ => none

def anyCid (bytes : List UInt8) : Bool :=
  match bytes with
  | 1 :: tail => (do
    let (_, tail) ← cidVarint? 9 tail
    let (_, tail) ← cidVarint? 9 tail
    let (length, tail) ← cidVarint? 9 tail
    pure (tail.length == length)).getD false
  | _ => false

def CidProfile.accepts : CidProfile → List UInt8 → Bool
  | .any => anyCid
  | .dasl => fun bytes => cidOk .exact .dasl (0 :: bytes)
  | .bdasl => fun bytes => cidOk .exact .bdasl (0 :: bytes)

abbrev Cid (profile : CidProfile := .any) := { bytes : List UInt8 // profile.accepts bytes = true }

/-- Binary CID adapters allow fixed-layout representations without changing either tree. -/
structure CidCodec (Link : Type) where
  bytes : Link → List UInt8
  parse? : List UInt8 → Option Link

def Cid.codec (profile : CidProfile := .any) : CidCodec (Cid profile) where
  bytes cid := cid.val
  parse? bytes := if accepted : profile.accepts bytes = true then some ⟨bytes, accepted⟩ else none

def cidAlphabet : Base32.Alphabet :=
  Radix.Alphabet.ofTable (fun digit =>
    Char.ofNat (if digit.val < 26 then 97 + digit.val else 24 + digit.val)) (by decide) (by decide)

def CidCodec.render {Link : Type} (codec : CidCodec Link) (value : Link) : String :=
  String.ofList ('b' :: Base32.encodeChars cidAlphabet false (codec.bytes value))

def CidCodec.read? {Link : Type} (codec : CidCodec Link) (text : String) : Option Link := do
  let 'b' :: digits := text.toList | none
  codec.parse? (← Base32.decodeChars cidAlphabet false digits)

end Silmaril.Formats.Cbor.Drisl
