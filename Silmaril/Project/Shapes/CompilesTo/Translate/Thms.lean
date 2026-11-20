module

public import Silmaril.Project.Shapes.CompilesTo.Translate.Defs
public import Silmaril.Project.CompilesTo.Thms
import Silmaril.Proofs.Project.Shapes.CompilesTo.Translate

/-!
# C ⇒ C translations: theorems

* `CanonicalRefines.refuted_of_ends`: two evaluated canonical runs on the same arguments, the
  source's ending with the integer `m` and the target's with another integer `k`, refute the
  translation (`¬ CanonicalRefines F G`). The source's run is forced, so it is the source's only
  run (`Forced.terminal_unique`); evaluating the target's run suffices for the target.

Proofs: `Silmaril.Proofs.Project.Shapes.CompilesTo.Translate`.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.CompilesTo

open Silmaril.Cerberus.Core.Dynamics (State)
open Silmaril.Project.CompilesTo (forcedRun)
open Silmaril.Project.Shapes.C (CFn)
open Silmaril.X86.SystemV.CApi (Signature Arguments)

/-- **A refutation from two evaluated runs.** -/
theorem CanonicalRefines.refuted_of_ends {sig : Signature} (F G : CFn sig)
    (a : Arguments sig.arguments) {nF nG : Nat} {m k : Int}
    (hF : endsInt m (forcedRun F.file F.labels nF (F.canonicalEntry a)) = true)
    (hG : endsInt k (forcedRun G.file G.labels nG (G.canonicalEntry a)) = true) (hne : m ≠ k) :
    ¬ CanonicalRefines F G :=
  Silmaril.Proofs.Project.Shapes.CompilesTo.Translate.not_refines_of_ends F G a hF hG hne

end Silmaril.Project.Shapes.CompilesTo

end
