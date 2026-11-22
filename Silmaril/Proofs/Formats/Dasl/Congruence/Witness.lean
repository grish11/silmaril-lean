module

public import Silmaril.Formats.Dasl.Congruence.Witness.Defs

public section

namespace Silmaril.Proofs.Formats.Dasl.CongruenceWitness

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.CongruenceWitness

variable {Name : Type} [LinearOrder Name] {certificate : Certificate Name} {base extended : Store Name}

theorem valid_mono {allowed : Link Name → Prop}
    (valid : certificate.Valid base allowed) (incl : base.Subset extended) : certificate.Valid extended allowed := by
  refine ⟨?_, valid.2⟩
  intro name tree lookup
  obtain ⟨⟨root, bindings⟩, policy⟩ := valid.1 lookup
  exact ⟨⟨incl.1 root, ⟨fun _ _ hit => incl.1 (bindings.1 hit), fun _ _ hit => incl.2 (bindings.2 hit)⟩⟩, policy⟩

end Silmaril.Proofs.Formats.Dasl.CongruenceWitness
