module

public import Silmaril.Containers.Ports.Defs
public import Silmaril.Containers.Lps.Thms
public import Silmaril.Containers.Image.Thms

/-!
# Proofs: published ports

Proofs for `Silmaril.Containers.Ports.Thms`. Nothing imports this module except that header.
-/

@[expose] public section

namespace Silmaril.Proofs.Containers.Ports

open Silmaril.Containers Silmaril.Containers.Ports
open Silmaril.Process.LPS

theorem publishedBind_nil (i : SyscallInput) : publishedBind [] i = false := by
  unfold publishedBind
  cases readBytesMap i.mem (i.arg 1) (zw (sint32 (i.arg 2))) <;> simp

theorem publish_nil : publish [] = Probes.spec := by
  funext i m o
  simp [publish, publishedBind_nil]

theorem publish_of_not {ports : List Nat} {i : SyscallInput} (h : publishedBind ports i = false)
    (m : Model) (o : Outcome SyscallEffect) : publish ports i m o ↔ Probes.spec i m o := by
  simp [publish, h]

theorem publish_of_published {ports : List Nat} {i : SyscallInput} (h : publishedBind ports i = true)
    (m : Model) (o : Outcome SyscallEffect) :
    publish ports i m o ↔ bindSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2) (zeroPort i (i.arg 1)) m o := by
  simp [publish, h]

end Silmaril.Proofs.Containers.Ports
