module

public import Silmaril.Wasi.Component.Consequence.Checkers.Thms
public import Silmaril.Logic.Consequence.Defs
public import Silmaril.Logic.Consequence.Structural.Defs

/-! # Consequence protocols as consequence systems

The protocol readings in the vocabulary of `Silmaril.Logic.Consequence`:

* `Accepted T r` is a `Silmaril.Consequence.System X C` (`accepted_system`), and the play
  witnesses `AcceptWitness T r` form a `WSystem` erasing to it (`erase_acceptWitness`).
* `Sound`/`Complete` of `Silmaril.Wasi.Consequence` are `System.Sound`/`System.Complete`
  (`sound_iff`, `complete_iff`).
* The structural hypotheses of the policy bridges are the named rules of
  `Silmaril.Consequence.Structural`: permutation closure is `Exchange`
  (`sound_perm_closure_of_exchange`), and the list-to-finite-set bridge needs only `WeakSubset`
  of the target (`finset_sound_of_weakSubset`).
* The membership checker's relation is `Reflexive`, and it is contained in every reflexive
  relation (`reflexive_memberChecker`, `memberChecker_sound_of_reflexive`): it is the least
  reflexive list-sequent relation. This is a property of the specification strategy, not of any
  compiled component.

New theorems (no source).
-/

@[expose] public section

namespace Silmaril.Wasi.Consequence

open Silmaril.Consequence (System WSystem)
open Silmaril.Consequence.Structural
open Silmaril.Wasi.Accept (Traces)
open Silmaril.Wasm.Component (Val)

universe u v u₁ u₂

variable {X : Type u} {C : Type v} {T : Set (List WEv)} {r : Reading X C}

/-- `Accepted T r` is a consequence system. -/
theorem accepted_system : (Accepted T r : System X C) = Accepted T r := rfl

/-- **The play witnesses erase to acceptance.** -/
theorem erase_acceptWitness :
    WSystem.erase (AcceptWitness T r : WSystem X C) = Accepted T r :=
  funext fun _ => funext fun _ => propext nonempty_acceptWitness_iff

theorem sound_iff {R target : X → C → Prop} : Sound R target ↔ System.Sound R target :=
  ⟨fun h x c => h x c, fun h x c => h x c⟩

theorem complete_iff {R target : X → C → Prop} : Complete R target ↔ System.Complete R target :=
  ⟨fun h x c => h x c, fun h x c => h x c⟩

variable {A : Type u₁}

/-- Permuting assumptions, for a target closed under `Exchange`. -/
theorem sound_perm_closure_of_exchange {R target : Rel A} (hs : Sound R target)
    (hx : Exchange target) : Sound (fun ys c => ∃ xs, xs.Perm ys ∧ R xs c) target :=
  sound_perm_closure hs fun _ _ _ hp ht => hx hp ht

/-- **Lists to finite sets, for a target closed under `WeakSubset`.** -/
theorem finset_sound_of_weakSubset [DecidableEq A] {stepOf : WEv → Option (Step A)}
    {claim : WEv → Option (A × Answer)} {target : Rel A}
    (hs : Sound (Accepted T (stateful Policy.list stepOf claim)) target)
    (hw : WeakSubset target) :
    Sound (Accepted T (stateful Policy.finset stepOf claim))
      fun s c => ∀ xs : List A, xs.toFinset = s → target xs c :=
  finset_sound_of_mem_closed hs fun _ _ _ h ht => hw (fun a ha => (h a).1 ha) ht

variable {D : Type} [DecidableEq D] {encL : List D → Val} {encC : D → Val}
  {decM : List Val → Option (List D × D)}

/-- **The membership checker is reflexive.** -/
theorem reflexive_memberChecker
    (hdec : ∀ args q, decM args = some q ↔ args = [encL q.1, encC q.2]) :
    Reflexive (Accepted (Traces (memberChecker encL encC)) (exportCheck checkFn decM)) :=
  fun Γ c h => (accepted_memberChecker hdec Γ c).2 h

/-- **…and it is contained in every reflexive relation**: the least reflexive one. -/
theorem memberChecker_sound_of_reflexive
    (hdec : ∀ args q, decM args = some q ↔ args = [encL q.1, encC q.2]) {target : Rel D}
    (ht : Reflexive target) :
    Sound (Accepted (Traces (memberChecker encL encC)) (exportCheck checkFn decM)) target :=
  fun Γ c h => ht ((accepted_memberChecker hdec Γ c).1 h)

end Silmaril.Wasi.Consequence
