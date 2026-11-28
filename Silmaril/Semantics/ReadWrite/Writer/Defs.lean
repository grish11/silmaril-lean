module

public import Silmaril.Semantics.ReadWrite.Abstraction.Thms
public import Mathlib.Control.Monad.Writer

/-!
Chronological access logs for Mathlib's Writer and WriterT. Log projections
describe recorded accesses. Replay and validation use the original valued trace.
-/

@[expose] public section
namespace Silmaril.Semantics.ReadWrite

universe u v w
variable {Address : Type u} {Value : Type v}

abbrev ValueLog (Address : Type u) (Value : Type v) := FreeMonoid (Event Address Value)
abbrev AddressLog (Address : Type u) := FreeMonoid (AddressEvent Address)
abbrev EntryLog (Address : Type u) (Value : Type v) := FreeMonoid (Address × Value)
abbrev AddressListLog (Address : Type u) := FreeMonoid Address

def Trace.toLog (trace : Trace Address Value) : ValueLog Address Value := FreeMonoid.ofList trace

def AddressTrace.toLog (trace : AddressTrace Address) : AddressLog Address := FreeMonoid.ofList trace

def ValueLog.eraseValues : ValueLog Address Value →* AddressLog Address :=
  FreeMonoid.map Event.eraseValue

def ValueLog.reads : ValueLog Address Value →* EntryLog Address Value where
  toFun log := FreeMonoid.ofList (Trace.reads log.toList)
  map_one' := rfl
  map_mul' _ _ := congrArg FreeMonoid.ofList Trace.reads_append

def ValueLog.writes : ValueLog Address Value →* EntryLog Address Value where
  toFun log := FreeMonoid.ofList (Trace.writes log.toList)
  map_one' := rfl
  map_mul' _ _ := congrArg FreeMonoid.ofList Trace.writes_append

def EntryLog.eraseValues : EntryLog Address Value →* AddressListLog Address :=
  FreeMonoid.map Prod.fst

def AddressLog.reads : AddressLog Address →* AddressListLog Address where
  toFun log := FreeMonoid.ofList (AddressTrace.reads log.toList)
  map_one' := rfl
  map_mul' _ _ := congrArg FreeMonoid.ofList List.filterMap_append

def AddressLog.writes : AddressLog Address →* AddressListLog Address where
  toFun log := FreeMonoid.ofList (AddressTrace.writes log.toList)
  map_one' := rfl
  map_mul' _ _ := congrArg FreeMonoid.ofList List.filterMap_append

def AddressListLog.toSet : AddressListLog Address →* AddressSet Address where
  toFun log := ⟨{address | address ∈ log.toList}⟩
  map_one' := AddressSet.ext (Set.ext fun address => List.mem_nil_iff address)
  map_mul' _ _ := AddressSet.ext (Set.ext fun _ => List.mem_append)

def AddressLog.accessSets : AddressLog Address →* AccessSets Address where
  toFun log := AddressTrace.accessSets log.toList
  map_one' := AccessSets.ext (Set.ext fun address => List.mem_nil_iff address)
    (Set.ext fun address => List.mem_nil_iff address)
  map_mul' first last := AddressTrace.accessSets_append first.toList last.toList

def AddressLog.useDef : AddressLog Address →* UseDef Address :=
  FreeMonoid.lift AddressEvent.useDef

def ValueLog.accessSets : ValueLog Address Value →* AccessSets Address :=
  AddressLog.accessSets.comp eraseValues

def ValueLog.useDef : ValueLog Address Value →* UseDef Address :=
  AddressLog.useDef.comp eraseValues

def AccessSets.readsLog : AccessSets Address →* AddressSet Address where
  toFun sets := ⟨sets.reads⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def AccessSets.defsLog : AccessSets Address →* AddressSet Address where
  toFun sets := ⟨sets.defs⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def AccessSets.footprintLog : AccessSets Address →* AddressSet Address where
  toFun sets := ⟨sets.footprint⟩
  map_one' := AddressSet.ext (Set.empty_union _)
  map_mul' _ _ := AddressSet.ext (Set.union_union_union_comm _ _ _ _)

def UseDef.defsLog : UseDef Address →* AddressSet Address where
  toFun summary := ⟨summary.defs⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def UseDef.footprintLog : UseDef Address →* AddressSet Address where
  toFun summary := ⟨summary.footprint⟩
  map_one' := AddressSet.ext (Set.empty_union _)
  map_mul' first last := AddressSet.ext (UseDef.footprint_mul first last)

abbrev ValueWriter (Address Value : Type u) := Writer (ValueLog Address Value)
abbrev AddressWriter (Address : Type u) := Writer (AddressLog Address)
abbrev AccessSetsWriter (Address : Type u) := Writer (AccessSets Address)
abbrev UseDefWriter (Address : Type u) := Writer (UseDef Address)

/-- Pair a completed observation with its result for ordinary Writer sequencing. -/
def Trace.record {Address Value Result : Type u} (trace : Trace Address Value) (result : Result) :
    ValueWriter Address Value Result :=
  WriterT.mk (result, trace.toLog)

namespace WriterLog

variable {First Second : Type u} {m : Type u → Type w} [Monad m] {α : Type u}

/-- Change a WriterT log via a monoid homomorphism, preserving the underlying effect and result. -/
abbrev mapLog [Monoid First] [Monoid Second] (f : First →* Second) :
    WriterT First m α → WriterT Second m α :=
  WriterT.adapt f

end WriterLog

end Silmaril.Semantics.ReadWrite
