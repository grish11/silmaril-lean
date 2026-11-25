module

public import Silmaril.Machine.Region.X86.SqliteStrLength.Clang.Defs
public import Silmaril.X86.Open.Thms
import Silmaril.Proofs.Machine.Region.X86.SqliteStrLength.Clang

@[expose] public section
namespace Silmaril.Machine.Region.X86.SqliteStrLength.Clang

open Silmaril.X86
open Silmaril.SSA.LambdaRTL

/-- Admitted entries reach their first return through the corresponding graph blocks. -/
theorem bridge_exists {entry : MState} (loaded : Ext.Loaded entry.memory entry.core.rip code)
    (saved : ReturnSlot entry) (ready : DataReady entry) :
    ∃ final, FnContract.FirstReturn Open.isa entry final ∧ Bridge entry final :=
  Proofs.Machine.Region.X86.SqliteStrLength.Clang.bridge_exists loaded saved ready

/-- Every first return in the admitted profile follows the same graph path. -/
theorem bridge_of_firstReturn {entry final : MState} (loaded : Ext.Loaded entry.memory entry.core.rip code)
    (saved : ReturnSlot entry) (ready : DataReady entry) (actual : FnContract.FirstReturn Open.isa entry final) :
    Bridge entry final :=
  Proofs.Machine.Region.X86.SqliteStrLength.Clang.bridge_of_firstReturn loaded saved ready actual

/-- On the same input store and memory, the viewed Clang and GCC graphs agree
on the exit, payload and full final store. This equality includes failed IR reads. -/
theorem viewed_run (entry : MState) :
    (fun out => (exitView out.1, out.2)) <$> graph.run (model entry.memory) (entryStore entry) =
      SqliteStrLength.graph.run (model entry.memory) (entryStore entry) :=
  Proofs.Machine.Region.X86.SqliteStrLength.Clang.viewed_run entry

end Silmaril.Machine.Region.X86.SqliteStrLength.Clang
