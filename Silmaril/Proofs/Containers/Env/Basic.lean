module

public import Silmaril.Containers.Env.Defs

/-!
# Proofs: environment interaction

Proofs for `Silmaril.Containers.Env.Thms`. Nothing imports this module except that header.
-/

public section

namespace Silmaril.Proofs.Containers.Env

open Silmaril.Containers Silmaril.Containers.Profile

theorem vsock_network_disjoint (c : Cap) :
    ¬ (vsockOnly c = true ∧ networkUnix c = true) := by
  rintro ⟨h₁, h₂⟩
  cases c with
  | sock f t => cases f <;> cases t <;> simp_all [vsockOnly, networkUnix, networkOnly, sup,
      tcpOnly, udpOnly, unixSockets]
  | _ => simp [vsockOnly] at h₁

end Silmaril.Proofs.Containers.Env
