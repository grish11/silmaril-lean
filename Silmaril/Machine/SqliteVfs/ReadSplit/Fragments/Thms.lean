module

public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Defs
import Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.Serial

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.ReadSplit.Fragments

/-- For any total handler, record its actual typed history and final state. -/
theorem read_fragments_trace {State : Type} (step : Handler State) (handle : Handle)
    (state : State) (offset count : Nat) (rest : List Nat) :
    let result := readFragments step handle state offset count rest
    Trace.Valid step state result.trace result.file ∧
      result.trace.map Exchange.request = fragmentRequests handle offset (count :: rest) :=
  Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.read_fragments_trace
    step handle state offset count rest

/-- Positive fragments of an admitted signed range recover the whole-read
reply and final file view. Both schedules retain their own valid traces. -/
theorem read_fragments_sound {State : Type} {step : Handler State} {view : State → FileState}
    (law : ReadLaw step view) (state : State) (handle : Handle)
    (offset count : Nat) (rest : List Nat) (countPositive : 0 < count)
    (restPositive : ∀ n ∈ rest, 0 < n) (admitted : ReadRange offset (count + rest.sum : Nat))
    (live : ((view state).mode handle).isNone = false) :
    let result := readFragments step handle state offset count rest
    let request := Request.read handle offset (count + rest.sum : Nat)
    let whole := step state request
    result.reply = some whole.1 ∧ view result.file = view whole.2 ∧
      Trace.Valid step state result.trace result.file ∧
      result.trace.map Exchange.request = fragmentRequests handle offset (count :: rest) ∧
      Trace.Valid step state [⟨request, whole.1⟩] whole.2 :=
  Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.read_fragments_sound
    law state handle offset count rest countPositive restPositive admitted live

end Silmaril.Machine.SqliteVfs.ReadSplit.Fragments
