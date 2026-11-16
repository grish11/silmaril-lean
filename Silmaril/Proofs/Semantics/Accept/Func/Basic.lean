module

public import Silmaril.Semantics.Accept.Func.Defs
public import Mathlib.Data.PFun

/-! # Proofs: the functional shape of relations

Proofs for `Silmaril.Semantics.Accept.Func.Thms`. Nothing imports this module except that
header.
-/

@[expose] public section

namespace Silmaril.Proofs.Semantics.Accept.Func

open Silmaril.Accept
open scoped SetRel

universe u v

variable {α : Type u} {β : Type v} {R : α -|> β} {a : α} {b : β}

theorem singleValued_iff_exists_pfun : SingleValued R ↔ ∃ f : α →. β, f.graph' = R := by
  refine ⟨fun h => ⟨fun a => ⟨∃ b, a ~[R] b, fun hb => hb.choose⟩, ?_⟩, ?_⟩
  · ext ⟨a, b⟩
    simp only [PFun.graph', Set.mem_ofPred_eq, Part.mem_mk_iff]
    exact ⟨fun ⟨hb, e⟩ => e ▸ hb.choose_spec,
      fun hb => ⟨⟨b, hb⟩, h (⟨b, hb⟩ : ∃ b, a ~[R] b).choose_spec hb⟩⟩
  · rintro ⟨f, rfl⟩
    exact fun _ _ _ hb hb' => Part.mem_unique hb hb'

theorem mem_toPartial (h : toPartial R a = some b) : a ~[R] b := by
  unfold toPartial at h
  split at h
  · rename_i hx; cases h; exact hx.choose_spec
  · cases h

theorem toPartial_eq_none : toPartial R a = none ↔ ∀ b, ¬ a ~[R] b := by
  unfold toPartial; split <;> simp_all

theorem toPartial_eq_some (hs : SingleValued R) : toPartial R a = some b ↔ a ~[R] b := by
  refine ⟨mem_toPartial, fun hb => ?_⟩
  cases h : toPartial R a with
  | none => exact absurd hb (toPartial_eq_none.1 h b)
  | some b' => exact congrArg some (hs (mem_toPartial h) hb)

theorem pdom_toPartial : pdom (toPartial R) = R.dom := by
  ext a; cases h : toPartial R a
  · simp [pdom, h, (toPartial_eq_none.1 h)]
  · simp [pdom, h]; exact ⟨_, mem_toPartial h⟩

theorem injective_ofPartial_iff {f : α → Option β} :
    Injective (ofPartial f) ↔ Set.InjOn f (pdom f) := by
  constructor
  · intro h a ha a' _ e
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 ha
    exact h (a := a) (b := b) hb (show f a' = some b from e ▸ hb)
  · intro h a a' b hb hb'
    have hb : f a = some b := hb; have hb' : f a' = some b := hb'
    exact h (by simp [pdom, hb]) (by simp [pdom, hb']) (hb.trans hb'.symm)

end Silmaril.Proofs.Semantics.Accept.Func
