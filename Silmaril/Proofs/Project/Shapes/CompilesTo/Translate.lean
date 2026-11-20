module

public import Silmaril.Project.Shapes.CompilesTo.Translate.Defs
public import Silmaril.Project.CompilesTo.Thms
public import Silmaril.Cerberus.Core.Forced.Thms

/-!
# C ⇒ C translations: refutation from forced runs

`not_refines_of_forced`: if the source's canonical entry on `a` has a forced run (every state one
successor) halting with a defined value, and the target's canonical entry on `a` has a forced
run halting with another outcome, the target does not refine the source. The source is safe
(`safe_of_forced`), the target halts with its outcome, and every halted state the source reaches
is the end of its forced run (`Forced.terminal_unique`), so the source cannot halt with the
target's outcome.
-/

@[expose] public section

namespace Silmaril.Proofs.Project.Shapes.CompilesTo.Translate

open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Project.CompilesTo
open Silmaril.Project.Shapes.CompilesTo
open Silmaril.Project.Shapes.C (CFn)
open Silmaril.X86.SystemV.CApi (Signature Arguments)

theorem reaches_rtg {file : Program} {labels : Labels} {s t : State}
    (h : Silmaril.Cerberus.Core.Forced.Reaches file labels s t) :
    Relation.ReflTransGen (fun a b => ∃ act, Step file labels a act b) s t := by
  induction h with
  | refl => exact .refl
  | cons edge _ _ ih => exact .head ⟨_, edge⟩ ih

theorem not_refines_of_forced {sig : Signature} (F G : CFn sig) (a : Arguments sig.arguments)
    {nF nG : Nat} {hF hG : State} {v : Val} {oG : Outcome}
    (runF : forcedRun F.file F.labels nF (F.canonicalEntry a) = some hF)
    (endF : hF.control = .halt (.defined v))
    (runG : forcedRun G.file G.labels nG (G.canonicalEntry a) = some hG)
    (endG : hG.control = .halt oG) (differ : oG ≠ .defined v) :
    ¬ CanonicalRefines F G := by
  intro h
  have pathF := (forcedRun_sound _ _ _ runF).1
  have safeF : (F.source []).Safe (F.canonicalEntry a) :=
    safe_of_forced (F := ⟨sig, F, 0, [], 0, []⟩) pathF endF
  obtain ⟨t, reach, halted⟩ :=
    h a safeF oG ⟨hG, reaches_rtg (forcedRun_sound _ _ _ runG).1, endG⟩
  have := Silmaril.Cerberus.Core.Forced.terminal_unique pathF endF reach halted
  subst this
  rw [endF] at halted
  injection halted with ho
  exact differ ho.symm

theorem of_endsInt {n : Int} {r : Option State} (h : endsInt n r = true) :
    ∃ hs, r = some hs ∧ hs.control = .halt (.defined (.loaded (.specified (.integer n)))) := by
  unfold endsInt at h
  split at h
  · rename_i hs
    split at h
    · rename_i m hc
      have : m = n := by simpa using h
      exact ⟨hs, rfl, this ▸ hc⟩
    · cases h
  · cases h

theorem not_refines_of_ends {sig : Signature} (F G : CFn sig) (a : Arguments sig.arguments)
    {nF nG : Nat} {m k : Int}
    (hF : endsInt m (forcedRun F.file F.labels nF (F.canonicalEntry a)) = true)
    (hG : endsInt k (forcedRun G.file G.labels nG (G.canonicalEntry a)) = true) (hne : m ≠ k) :
    ¬ CanonicalRefines F G := by
  obtain ⟨sF, rF, eF⟩ := of_endsInt hF
  obtain ⟨sG, rG, eG⟩ := of_endsInt hG
  refine not_refines_of_forced F G a rF eF rG eG ?_
  intro heq
  injection heq with hv
  injection hv with hl
  injection hl with hs
  injection hs with hi
  exact hne hi.symm

end Silmaril.Proofs.Project.Shapes.CompilesTo.Translate

end
