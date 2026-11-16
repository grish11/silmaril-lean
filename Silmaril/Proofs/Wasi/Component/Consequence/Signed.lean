module

public import Silmaril.Wasi.Component.Consequence.Signed.Defs
public import Silmaril.Wasi.Component.Consequence.Gentzen.Thms
public import Silmaril.Wasm.Examples.MemberCheck.Thms
public import Silmaril.Wasm.Examples.EmptyCheck.Thms

/-!
# Signed and two-sided observation protocols: proofs

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasi.Component.Consequence

open Silmaril.Wasi Silmaril.Wasi.Consequence
open Silmaril.Consequence (Signed)
open Silmaril.Consequence.Refutation (SatAll Unsat CheckSound)

universe u v

theorem accepted_swap {X : Type u} {C : Type v} {T : Set (List WEv)} {r : Reading X C} {x : X}
    {c : C} : Accepted T (swap r) c x ↔ Accepted T r x c := by
  simp only [Accepted, swap, Option.map_eq_some_iff]
  constructor
  · rintro ⟨s, e, hT, ⟨x', c', a'⟩, h, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact ⟨s, e, hT, h⟩
  · rintro ⟨s, e, hT, h⟩
    exact ⟨s, e, hT, _, h, rfl⟩

theorem satAll_of_subset {M F : Type} {sat : M → F → Prop} {m : M} {l l' : List F}
    (h : l' ⊆ l) (hs : SatAll sat m l) : SatAll sat m l' := fun x hx => hs x (h hx)

/-- **The finite-set lift of a sound UNSAT checker is sound**: unsatisfiability depends only on
the members. -/
theorem batchFinset_unsat {M V : Type} [DecidableEq V] {sat : M → Signed V → Prop}
    {T : Set (List WEv)} {r : Reading (List (Signed V)) Unit}
    (hs : CheckSound sat (batches T r)) {s : Finset (Signed V)} (h : batchFinset T r s) :
    Unsat sat s.toList := by
  obtain ⟨l, rfl, hl⟩ := h
  intro m hm
  exact hs l hl m (satAll_of_subset (fun x hx => by simpa using hx) hm)

theorem memberEnc_eq_some {Γ Δ w : List UInt8} :
    memberEnc Γ Δ = some w ↔ ∃ c, Δ = [c] ∧ w = c :: Γ := by
  match Δ with
  | [] => simp [memberEnc]
  | [c] => simp [memberEnc, eq_comm]
  | _ :: _ :: _ => simp [memberEnc]

end Silmaril.Proofs.Wasi.Component.Consequence
