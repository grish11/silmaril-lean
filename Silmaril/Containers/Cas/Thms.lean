module

public import Silmaril.Containers.Cas.Defs
import Silmaril.Proofs.Containers.Cas.Basic

/-!
# Content-addressed stores: theorems

PROVED (standard axioms). Proofs longer than a few lines are in
`Silmaril.Proofs.Containers.Cas` and only pointed at from here.

* `sound_empty`, `sound_put`: building a store by putting contents under their own digests
  keeps integrity;
* `sound_checked`: **checking establishes integrity** whatever the source store returns;
  `checked_of_sound`: on a sound store, checking changes nothing;
* `agree_of_sound`: two sound stores give the same content for a digest **when the hash binds**
  on their contents;
* `digest_not_binding`: integrity alone does not pin contents: two sound stores for a
  colliding hash return different contents for the same digest;
* `unchecked_unsound`: without checking, a store can return anything under any digest;
* `sound_decode`: integrity transfers from bytes to decoded contents along a decoder that is
  left-inverse to an encoder (the refinement step from OCI octets to abstract contents).
-/

public section

namespace Silmaril.Containers.Cas.Store

variable {D C C' : Type}

theorem sound_empty (h : C → D) : Sound h (empty : Store D C) := by
  intro d c hc; cases hc

theorem sound_put [DecidableEq D] {h : C → D} {S : Store D C} (hS : Sound h S) (c : C) :
    Sound h (S.put h c) := Silmaril.Proofs.Containers.Cas.sound_put hS c

theorem sound_checked [DecidableEq D] (h : C → D) (S : Store D C) : Sound h (S.checked h) :=
  Silmaril.Proofs.Containers.Cas.sound_checked h S

theorem checked_of_sound [DecidableEq D] {h : C → D} {S : Store D C} (hS : Sound h S) :
    S.checked h = S := Silmaril.Proofs.Containers.Cas.checked_of_sound hS

theorem agree_of_sound {h : C → D} {S T : Store D C} (hS : Sound h S) (hT : Sound h T)
    (hinj : InjOn h (fun c => S.Holds c ∨ T.Holds c)) {d : D} {c c' : C}
    (hc : S d = some c) (hc' : T d = some c') : c = c' :=
  hinj c c' (.inl ⟨d, hc⟩) (.inr ⟨d, hc'⟩) ((hS d c hc).trans (hT d c' hc').symm)

/-- Integrity without binding: under a hash with a collision, two sound stores answer the same
digest with different contents. -/
theorem digest_not_binding :
    ∃ (h : Bool → Unit) (S T : Store Unit Bool),
      Sound h S ∧ Sound h T ∧ S () = some false ∧ T () = some true :=
  ⟨fun _ => (), fun _ => some false, fun _ => some true,
    fun _ _ _ => rfl, fun _ _ _ => rfl, rfl, rfl⟩

/-- A store that has not been checked can be unsound. -/
theorem unchecked_unsound : ∃ S : Store Bool Bool, ¬ Sound id S :=
  ⟨fun _ => some true, fun h => Bool.noConfusion (h false true rfl)⟩

theorem sound_decode {h : C → D} {S : Store D C} (hS : Sound h S) {dec : C → Option C'}
    {enc : C' → C} (hinv : ∀ c x, dec c = some x → enc x = c) :
    Sound (h ∘ enc) (S.decode dec) := Silmaril.Proofs.Containers.Cas.sound_decode hS hinv

end Silmaril.Containers.Cas.Store
