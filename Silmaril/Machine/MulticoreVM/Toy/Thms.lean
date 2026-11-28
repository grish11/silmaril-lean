module

public import Silmaril.Machine.MulticoreVM.Toy.Defs
public import Silmaril.Machine.MulticoreVM.Thms
import Silmaril.Proofs.Machine.MulticoreVM.Toy

public section

namespace Silmaril.Machine.MulticoreVM.Toy

open Silmaril.Semantics.ConcurrentTrace (Equivalent)

/-- Distinct ready emit instructions commute on the whole configuration. The chronological
words occur in opposite orders and represent the same concurrent trace. -/
theorem emit_commutes (cfg : Config) {a b : ThreadId} (distinct : a ≠ b)
    {x y : Nat} {p q : List Instr}
    (atA : cfg a = some ⟨x, .emit :: p⟩) (atB : cfg b = some ⟨y, .emit :: q⟩) :
    ∃ final,
      execute exec [⟨a, none⟩, ⟨b, none⟩] cfg = some (final, [.event a x, .event b y]) ∧
      execute exec [⟨b, none⟩, ⟨a, none⟩] cfg = some (final, [.event b y, .event a x]) ∧
      Equivalent [.event a x, .event b y] [.event b y, .event a x] :=
  Proofs.Machine.MulticoreVM.emit_commutes cfg distinct atA atB

end Silmaril.Machine.MulticoreVM.Toy
