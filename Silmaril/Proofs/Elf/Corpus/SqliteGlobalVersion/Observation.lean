module
public import Silmaril.Elf.Corpus.SqliteGlobalVersion.Context.Defs
namespace Silmaril.Proofs.Elf.Corpus.SqliteGlobalVersion
open Silmaril.Elf.Corpus.SqliteGlobalVersion.Context
/-- The diagnostic normalization cannot hide a real allocation-counter change. -/
public theorem allocation_counter_rejected (s : Silmaril.Cerberus.Mem.Concrete.State) :
    ¬ memoryUnchanged s {s with nextId := s.nextId + 1} := by
  intro h
  have hn := congrArg Silmaril.Cerberus.Mem.Concrete.State.nextId h
  change s.nextId + 1 = s.nextId at hn
  omega
/-- Matching numeric addresses do not erase the returned allocation identity. -/
public theorem wrong_allocation_rejected (address : Int) :
    returnedAddress (.loaded (.specified (.pointer (.allocated 0 address)))) = none := by
  rfl
/-- A null result cannot stand in for the actual global pointer return. -/
public theorem null_return_rejected (type : Silmaril.Cerberus.Ctype) :
    returnedAddress (.loaded (.specified (.pointer (.null type)))) = none := by
  rfl
end Silmaril.Proofs.Elf.Corpus.SqliteGlobalVersion
