module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Defs

/-! One uncompressed INT64 dictionary followed by dictionary and PLAIN data. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback

open Dictionary (DataPage CheckedChunk atFrame)

def admits (encoding : Int) : Bool :=
  encoding == 8 || encoding == 0

def isDictionary (page : DataPage) : Bool :=
  page.params.encoding == 8

/-- Only a nonempty dictionary prefix followed by a nonempty PLAIN suffix
constitutes fallback. The leading dictionary frame is outside this list. -/
def Ordered (data : List DataPage) : Prop :=
  ∃ references plain, data = references ++ plain ∧ references ≠ [] ∧ plain ≠ [] ∧
    (∀ page ∈ references, page.params.encoding = 8) ∧
    (∀ page ∈ plain, page.params.encoding = 0)

def checkSequence (data : List DataPage) : Except Leaf.Error Unit := do
  let first :: _ := data | throw .dictionaryMissingData
  if !isDictionary first then throw (atFrame 1 first.frame (.encoding first.params.encoding))
  let suffix := data.dropWhile isDictionary
  if suffix.isEmpty then throw .dictionaryMissingFallback
  let start := data.length - suffix.length + 1
  match (suffix.zipIdx start).find? (fun (page, _) => page.params.encoding != 0) with
  | none => return ()
  | some (page, index) => throw (atFrame index page.frame .dictionaryAfterFallback)

/-- Reuse the checked original chunk, dictionary frame, offsets and byte/row bounds. -/
def checkGroup (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (index : Nat) : Except Leaf.Error CheckedChunk :=
  Dictionary.checkGroupWith admits checkSequence limits leafLimits bound index

/-- The original data header selects one decoder. Each error retains its
wire page ordinal and absolute header offset. -/
def decodePage (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (entries : Array Int64) (page : DataPage) (ordinal : Nat) :
    Except Leaf.Error (List (Option Int64)) :=
  if page.params.encoding = 0 then
    (ScalarPage.decode .int64 page.params leafLimits.page (Internal.body bound page.frame)).mapError
      (atFrame ordinal page.frame ∘ .plain)
  else Dictionary.decodePage limits leafLimits bound entries page ordinal

/-- Exact nullable INT64 slots from the admitted branch on the original payload. -/
def PageWire (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (entries : Array Int64) (page : DataPage) (slots : List (Option Int64)) : Prop :=
  slots.length = page.params.numValues ∧
    ((page.params.encoding = 8 ∧
      DictionaryIndex.decode entries page.params leafLimits.page limits.indices
        (Internal.body bound page.frame) = .ok slots) ∨
     (page.params.encoding = 0 ∧
      ScalarPage.decode .int64 page.params leafLimits.page (Internal.body bound page.frame) = .ok slots))

def readGroup (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except Leaf.Error (Slots bound) := do
  let checked ← checkGroup limits leafLimits bound index
  let entries := checked.entries.toArray
  let pages ← (checked.data.zipIdx 1).mapM fun (page, ordinal) =>
    decodePage limits leafLimits bound entries page ordinal
  return pages.flatten.map (Option.map bound.binding.descriptor.decode)

def readBound (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound) :
    Events.ToIpc.Source :=
  Events.readBoundWith bound (readGroup limits leafLimits bound)

/-- Select the explicit uncompressed fallback profile at the supplied leaf ordinal. -/
def convert (profile : AnnotationProfile) (limits : Dictionary.Limits) (inputLimits : Events.ToIpc.Limits)
    (outputLimits : Arrow.ObservationLimits) (input : Bytes) (ordinal : Nat) :
    Except Events.ToIpc.Error KBytes :=
  Events.ToIpc.convertGroups profile inputLimits outputLimits input ordinal (readGroup limits inputLimits.leaf)

end Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback
