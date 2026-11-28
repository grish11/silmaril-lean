module

public import Silmaril.Languages.Starlark.Lists.GoDictionary.Deletion.Defs
public import Silmaril.Languages.Starlark.Lists.GoDictionary.Operational.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Lists.GoDictionary.Deletion

def Probes (heap : Heap) (table : Table) (key : Value) (hash : UInt32)
    (out : Except Lists.Error (Option (Address × Row))) : Prop :=
  Comparison.Probes (fun item => Comparison.EqualAt heap Comparison.defaultDepth key item.2.key)
    (table.candidates hash) out

/-- A miss or error leaves the input table intact. On a hit the selected
physical cell is cleared and the same address is removed from iteration. -/
inductive Deletes (heap : Heap) (table : Table) (key : Value) :
    Except Error (Option Value × Table) → Prop where
  | hashError {error : Error} : hashKey heap key = .error error →
      Deletes heap table key (.error error)
  | probeError {word : UInt32} {error : Lists.Error} :
      HashesAt heap (heap.size + 1) key word →
      Probes heap table key (storedHash word) (.error error) →
      Deletes heap table key (.error (.runtime error))
  | miss {word : UInt32} :
      HashesAt heap (heap.size + 1) key word →
      Probes heap table key (storedHash word) (.ok none) →
      Deletes heap table key (.ok (none, table))
  | hit {word : UInt32} {address : Address} {row : Row} :
      HashesAt heap (heap.size + 1) key word →
      Probes heap table key (storedHash word) (.ok (some (address, row))) →
      Deletes heap table key (.ok (some row.value, table.unlink address))

end Silmaril.Languages.Starlark.Lists.GoDictionary.Deletion
