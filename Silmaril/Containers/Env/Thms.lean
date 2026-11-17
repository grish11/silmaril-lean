module

public import Silmaril.Containers.Env.Defs
import Silmaril.Proofs.Containers.Env.Basic

/-!
# Environment interaction: theorems

PROVED (standard axioms). Longer proofs are in `Silmaril.Proofs.Containers.Env`.

* `Profile.le_refl`, `Profile.le_trans`, `Profile.le_sup_left`, `Profile.le_sup_right`: the
  inclusion order and union;
* the named profiles: `tcpOnly ≤ networkOnly`, `udpOnly ≤ networkOnly`,
  `networkOnly ≤ networkUnix`, `none ≤ P`;
* `Profile.vsock_network_disjoint`: no capability is both vsock and network/Unix;
* `Confined.mono`, `Confined.append`, `Confined.nil`: confinement is monotone in the profile
  and compositional in the trace;
* `Confined.eq_nil_of_disjoint`: a trace confined to two disjoint profiles has no events, so,
  for example, a run that is both vsock-only and TCP-only does nothing observable.
-/

public section

namespace Silmaril.Containers

namespace Profile

theorem le_refl (P : Profile) : P.Le P := fun _ h => h

theorem le_trans {P Q R : Profile} (h₁ : P.Le Q) (h₂ : Q.Le R) : P.Le R :=
  fun c h => h₂ c (h₁ c h)

theorem le_sup_left (P Q : Profile) : P.Le (P.sup Q) := fun c h => by simp [sup, h]

theorem le_sup_right (P Q : Profile) : Q.Le (P.sup Q) := fun c h => by simp [sup, h]

theorem none_le (P : Profile) : none.Le P := fun _ h => Bool.noConfusion h

theorem tcpOnly_le_networkOnly : tcpOnly.Le networkOnly := le_sup_left _ _

theorem udpOnly_le_networkOnly : udpOnly.Le networkOnly := le_sup_right _ _

theorem networkOnly_le_networkUnix : networkOnly.Le networkUnix := le_sup_left _ _

theorem vsock_network_disjoint (c : Cap) :
    ¬ (vsockOnly c = true ∧ networkUnix c = true) :=
  Silmaril.Proofs.Containers.Env.vsock_network_disjoint c

end Profile

theorem Confined.nil (P : Profile) : Confined P [] := fun _ h => nomatch h

theorem Confined.mono {P Q : Profile} (h : P.Le Q) {t : List Ev} (ht : Confined P t) :
    Confined Q t := fun e he => h _ (ht e he)

theorem Confined.append {P : Profile} {t u : List Ev} (ht : Confined P t) (hu : Confined P u) :
    Confined P (t ++ u) := fun e he => (List.mem_append.1 he).elim (ht e) (hu e)

theorem Confined.eq_nil_of_disjoint {P Q : Profile} (hd : ∀ c, ¬ (P c = true ∧ Q c = true))
    {t : List Ev} (hP : Confined P t) (hQ : Confined Q t) : t = [] := by
  cases t with
  | nil => rfl
  | cons e _ => exact (hd e.cap ⟨hP e (.head _), hQ e (.head _)⟩).elim

end Silmaril.Containers
