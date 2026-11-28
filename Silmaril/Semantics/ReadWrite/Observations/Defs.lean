module

public import Silmaril.Semantics.ReadWrite.Defs

/-! Observations between consecutive reads of one address. -/

@[expose] public section
namespace Silmaril.Semantics.ReadWrite

universe u v w
variable {Address : Type u} {Value : Type v} {State : Type w}

/-- If a read succeeds at the address just written, it returns the written value.
This law permits write-only addresses and writes that initialize backing storage. -/
def Access.ReadsAfterWrite (access : Access Address Value State) : Prop :=
  ∀ ⦃initial next address written observed⦄,
    access.write initial address written = some next →
    access.read next address = some observed → observed = written

namespace Trace

/-- The most recent value written at this address, if any. -/
def lastWrite [DecidableEq Address] : Trace Address Value → Address → Option Value
  | [], _ => none
  | .read _ _ :: rest, address => lastWrite rest address
  | .write p value :: rest, address =>
      (lastWrite rest address).or (if p = address then some value else none)

/-- Two reads at the address with no read of that address in the intervening
trace. The gap can contain accesses at other addresses and any number of writes. -/
def ConsecutiveReads (trace : Trace Address Value) (address : Address)
    (earlier : Value) (gap : Trace Address Value) (later : Value) : Prop :=
  ∃ pre post, trace = pre ++ .read address earlier :: (gap ++ .read address later :: post) ∧
    ¬ gap.Reads address

/-- All consecutive observations are equal. Vacuous with fewer than two reads. -/
def ReadsStable (trace : Trace Address Value) (address : Address) : Prop :=
  ∀ ⦃earlier gap later⦄, trace.ConsecutiveReads address earlier gap later → later = earlier

/-- Observations can differ only across a write to this address. Vacuous with
fewer than two reads, or when every pair of reads is separated by a write. -/
def ReadsStableWithoutWrites (trace : Trace Address Value) (address : Address) : Prop :=
  ∀ ⦃earlier gap later⦄, trace.ConsecutiveReads address earlier gap later →
    ¬ gap.Defs address → later = earlier

/-- Each later read equals the last intervening write to this address, or the
earlier read in the absence of such a write. Vacuous with fewer than two reads. -/
def ReadsMatchLastWrite [DecidableEq Address]
    (trace : Trace Address Value) (address : Address) : Prop :=
  ∀ ⦃earlier gap later⦄, trace.ConsecutiveReads address earlier gap later →
    later = (gap.lastWrite address).getD earlier

/-- Addresses with at least two reads. -/
def RepeatedReadAddresses (trace : Trace Address Value) : Address → Prop :=
  fun address => ∃ earlier gap later, trace.ConsecutiveReads address earlier gap later

def StableReadAddresses (trace : Trace Address Value) : Address → Prop :=
  fun address => trace.RepeatedReadAddresses address ∧ trace.ReadsStable address

def StableWithoutWritesAddresses (trace : Trace Address Value) : Address → Prop :=
  fun address => trace.RepeatedReadAddresses address ∧ trace.ReadsStableWithoutWrites address

def LastWriteCompatibleAddresses [DecidableEq Address] (trace : Trace Address Value) : Address → Prop :=
  fun address => trace.RepeatedReadAddresses address ∧ trace.ReadsMatchLastWrite address

/-- Addresses with an observed change across at least one consecutive read pair. -/
def ChangedReadAddresses (trace : Trace Address Value) : Address → Prop :=
  fun address => ∃ earlier gap later, trace.ConsecutiveReads address earlier gap later ∧ later ≠ earlier

end Trace
end Silmaril.Semantics.ReadWrite
