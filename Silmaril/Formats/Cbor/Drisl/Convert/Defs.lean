module

public import Silmaril.Formats.Cbor.Drisl.Number.Defs
public import Silmaril.Formats.JsonWithBytes.Traverse.Defs

@[expose] public section

namespace Silmaril.Formats.Cbor.Drisl

def mapNumber? {Input Output : Type} (number : Input → Option Output) :
    JsonWithBytes.Scalar Input → Option (JsonWithBytes.Scalar Output)
  | .null => some .null
  | .bool value => some (.bool value)
  | .string value => some (.string value)
  | .bytes value => some (.bytes value)
  | .number value => .number <$> number value

def removeLinks? {Numeric Link : Type} {index : JsonIx}
    (value : RawSyn String (Scalar Numeric Link) index) :
    Option (RawSyn String (JsonWithBytes.Scalar Numeric) index) :=
  JsonWithBytes.traverse? some (fun | .data scalar => some scalar | .link _ => none) value

def fromJsonWithBytes? {Link : Type} (value : JsonWithBytes.Ordered) : Option (Ordered Link) :=
  JsonWithBytes.traverse? some (fun scalar => .data <$> mapNumber? Number.ofDecimal? scalar) value

/-- View link-free CBOR data in the exact decimal model. Integer/float kind is
carried by the debug spelling; general decimal lowering need not keep that kind. -/
def toJsonWithBytes? {Link : Type} (value : Ordered Link) : Option JsonWithBytes.Ordered :=
  (removeLinks? value).bind (JsonWithBytes.traverse? some (mapNumber? (some ∘ Number.toDecimal)))

def jsonWithBytesI64? (value : JsonWithBytes.Ordered) : Option JsonWithBytes.OrderedI64 :=
  JsonWithBytes.traverse? some (mapNumber? decimalI64?) value

def widenScalar {Link : Type} : Scalar Int64 Link → Scalar Number Link
  | .link cid => .link cid
  | .data .null => .data .null
  | .data (.bool value) => .data (.bool value)
  | .data (.string value) => .data (.string value)
  | .data (.bytes value) => .data (.bytes value)
  | .data (.number value) => .data (.number (.integer (Integer.ofInt64 value)))

def widenATProto {Link : Type} (value : OrderedATProto Link) : Ordered Link :=
  value.mapScalar widenScalar

def narrowScalar? {Link : Type} : Scalar Number Link → Option (Scalar Int64 Link)
  | .link cid => some (.link cid)
  | .data scalar => .data <$> mapNumber? (fun
      | .integer integral => int64? integral.toInt
      | .float _ => none) scalar

def narrowATProto? {Link : Type} (value : Ordered Link) : Option (OrderedATProto Link) :=
  JsonWithBytes.traverse? some narrowScalar? value

/-- Reinterpret the binary representation of every link under another CID
adapter. Non-link data, keys, and order are not converted. -/
def recodeLinks? {Numeric Input Output : Type} (input : CidCodec Input) (output : CidCodec Output)
    {index : JsonIx} (value : RawSyn String (Scalar Numeric Input) index) :
    Option (RawSyn String (Scalar Numeric Output) index) :=
  JsonWithBytes.traverse? some (fun
    | .data data => some (.data data)
    | .link link => .link <$> output.parse? (input.bytes link)) value

end Silmaril.Formats.Cbor.Drisl
