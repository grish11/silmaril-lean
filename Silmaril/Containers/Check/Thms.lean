module

public import Silmaril.Containers.Check.Defs
public import Silmaril.Containers.Precondition.Thms
public import Silmaril.Semantics.Acceptors.Thms
import Silmaril.Proofs.Containers.Check.Basic

/-!
# Container obligations as consequence systems and acceptors: theorems

PROVED (standard axioms). Longer proofs are in `Silmaril.Proofs.Containers.Check`.

**The laws of the verified system** `vsys R`.

* `vsys_noUB`: every judgement `i ⊢ φ` excludes undefined behaviour of every run of `i`;
* `vsys_mono`, `vsys_and`: weakening of the conclusion, and conjunction;
* `vsys_sound_raw`: `vsys R` is sound for raw satisfaction `rawsys R` (the converse fails:
  `Silmaril.Containers.Mini.rawsys_not_sound`);
* `vsys_sound_of_le`: a runtime model with more runs proves less (`R ≤ R'` makes `vsys R'` sound
  for `vsys R`);
* `vsys_restrict_noUB`, `vsys_mayKill_noUB`: a judgement under an assumption or under runtime
  kills still excludes undefined behaviour of the unrestricted model: assumptions and kills do not
  mask it.

**Checkers.** `checkSys_sound_iff`: the system of a checker is sound for `vsys R` exactly when the
checker is `Accept.Sound` for the images satisfying the verification precondition;
`checkSys_sound_iff_vsufficient`: exactly when "the checker accepts" is a verified sufficient
precondition (`VSufficient`).

**The monitor.** `vmonitor_correctFold`, `vmonitor_correctInterleaved`: the monitor is correct
for its language in the fold and interleaved protocols; `vlang_iff`: a run has no undefined
behaviour and only allowed events exactly when all its observation prefixes are accepted.
-/

public section

namespace Silmaril.Containers.Check

open Silmaril.Containers Silmaril.Consequence

variable {I P P' E : Type}

theorem vsys_noUB {R : Runtime I P E} {i : I} {φ : Spec E} (h : vsys R i φ) :
    pre R Spec.noUB i := vpre_noUB h

theorem vsys_mono {R : Runtime I P E} {i : I} {φ ψ : Spec E} (hφ : ∀ b, φ b → ψ b)
    (h : vsys R i φ) : vsys R i ψ := fun b hb => ⟨(h b hb).1, hφ b (h b hb).2⟩

theorem vsys_and (R : Runtime I P E) (i : I) (φ ψ : Spec E) :
    vsys R i (fun b => φ b ∧ ψ b) ↔ vsys R i φ ∧ vsys R i ψ :=
  ⟨fun h => ⟨fun b hb => ⟨(h b hb).1, (h b hb).2.1⟩, fun b hb => ⟨(h b hb).1, (h b hb).2.2⟩⟩,
    fun ⟨h₁, h₂⟩ b hb => ⟨(h₁ b hb).1, (h₁ b hb).2, (h₂ b hb).2⟩⟩

theorem vsys_sound_raw (R : Runtime I P E) : System.Sound (vsys R) (rawsys R) :=
  fun _ _ h b hb => (h b hb).2

theorem vsys_sound_of_le {R : Runtime I P E} {R' : Runtime I P' E} (h : R.Le R') :
    System.Sound (vsys R') (vsys R) := fun _ _ h' => pre_antitone h h'

theorem vsys_restrict_noUB {R : Runtime I P E} {A : Spec E} {i : I} {φ : Spec E}
    (h : vsys (R.restrict A) i φ) : pre R Spec.noUB i :=
  (Runtime.noUB_restrict_iff R A i).1 (vsys_noUB h)

theorem vsys_mayKill_noUB {R : Runtime I P E} {ks : Kill → Prop} {i : I} {φ : Spec E}
    (h : vsys (R.mayKill ks) i φ) : pre R Spec.noUB i :=
  (Runtime.noUB_mayKill_iff R ks i).1 (vsys_noUB h)

theorem checkSys_sound_iff (R : Runtime I P E) (check : I → Bool) (φ : Spec E) :
    System.Sound (checkSys check φ) (vsys R) ↔ Silmaril.Accept.Sound check (vset R φ) :=
  Silmaril.Proofs.Containers.Check.checkSys_sound_iff R check φ

theorem checkSys_sound_iff_vsufficient (R : Runtime I P E) (check : I → Bool) (φ : Spec E) :
    System.Sound (checkSys check φ) (vsys R) ↔ VSufficient R (fun i => check i = true) φ :=
  checkSys_sound_iff R check φ

theorem vmonitor_correctFold (ok : E → Bool) : (vmonitor ok).CorrectFold (vlang ok) :=
  Silmaril.Proofs.Containers.Check.vmonitor_correctFold ok

theorem vmonitor_correctInterleaved (ok : E → Bool) :
    (vmonitor ok).CorrectInterleaved (vlang ok) :=
  Silmaril.Proofs.Containers.Check.vmonitor_correctInterleaved ok

theorem vlang_iff (ok : E → Bool) (b : Beh E) :
    (Spec.noUB b ∧ Spec.always (fun e => ok e = true) b) ↔
      ∀ w, ObsPrefix b w → w ∈ vlang ok :=
  Silmaril.Proofs.Containers.Check.vlang_iff ok b

end Silmaril.Containers.Check
