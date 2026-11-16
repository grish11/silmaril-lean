module

public import Silmaril.Wasi.Component.Accept.Strict.Thms
public import Silmaril.Proofs.Wasi.Component.Accept.Acceptor

/-!
# The verdict components: proofs

`verdictComponent A R` is a generated strategy. Its `true` returns of `accept` carry exactly
the strings of `A`, and its `false` returns of `reject` exactly those of `R`
(`Strategy.accepted_generate`; both observations read Proponent moves only). Its combined
language is therefore `A \ R`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasi.Component.Accept

open Silmaril.Games Silmaril.Games.Accept Silmaril.Formats.Accept Silmaril.Wasi
  Silmaril.Wasi.Accept
open Silmaril.Wasm.Component (Val)

variable {α : Type} {f : FnName} {dec : List Val → Option α}

/-- Export answers returning `false` are Proponent moves. -/
theorem exportFalseObs_not_isO {I X : Set FnName} (m : Move (nsig I) (nsig X)) (a : α)
    (h : (exportFalseObs f dec ∘ wev) m = some a) : ¬ m.IsO := by
  rcases m with (_ | _) | (_ | _) <;> simp_all [exportFalseObs, wev, Move.IsO]

theorem legal_two {I X : Set FnName} (q : (nsig X).Op) (r : (nsig X).Ar q) :
    Legal ([.inr (.ask q), .inr (.ans q r)] : List (Move (nsig I) (nsig X))) :=
  ⟨_, .cons (.ask _) (.cons (.ret _ _) (.nil _))⟩

theorem exportBytesLang_verdictComponent (A R : ByteLang) :
    exportBytesLang (verdictComponent A R) acceptFn = A := by
  change exportAccepted (verdictComponent A R) acceptFn (args1 bytes?) = (A : Set (List UInt8))
  rw [exportAccepted_eq, verdictComponent, Strategy.accepted_generate exportObs_not_isO]
  ext w
  constructor
  · rintro ⟨s, ⟨hs, -⟩, m, hm, ho⟩
    rcases hs with ⟨w', hw', rfl⟩ | ⟨w', -, rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · simp [exportObs, wev] at ho
      · simp only [Function.comp_apply, wev, exportObs, ite_true, args1, bytesVal,
          bytes?_bytesV_toBitVec, Option.some.injEq] at ho
        exact ho ▸ hw'
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl <;> simp [exportObs, wev] at ho
  · intro hw
    refine ⟨_, ⟨.inl ⟨w, hw, rfl⟩, legal_two _ _⟩, _,
      List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    simp only [Function.comp_apply, wev, exportObs, ite_true, args1, bytesVal,
      bytes?_bytesV_toBitVec]

theorem exportRejected_verdictComponent (A R : ByteLang) :
    exportRejected (verdictComponent A R) rejectExport (args1 bytes?) = R := by
  rw [exportRejected_eq, verdictComponent, Strategy.accepted_generate exportFalseObs_not_isO]
  ext w
  constructor
  · rintro ⟨s, ⟨hs, -⟩, m, hm, ho⟩
    rcases hs with ⟨w', -, rfl⟩ | ⟨w', hw', rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl <;> simp [exportFalseObs, wev] at ho
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · simp [exportFalseObs, wev] at ho
      · simp only [Function.comp_apply, wev, exportFalseObs, ite_true, args1, bytesVal,
          bytes?_bytesV_toBitVec, Option.some.injEq] at ho
        exact ho ▸ hw'
  · intro hw
    refine ⟨_, ⟨.inr ⟨w, hw, rfl⟩, legal_two _ _⟩, _,
      List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    simp only [Function.comp_apply, wev, exportFalseObs, ite_true, args1, bytesVal,
      bytes?_bytesV_toBitVec]

/-- **The combined language of the verdict component is `A \ R`.** -/
theorem strict_verdictComponent (A R : ByteLang) :
    exportAcceptedNotRejected (verdictComponent A R) acceptFn rejectExport (args1 bytes?) =
      (A : Set (List UInt8)) \ R := by
  have h₁ := exportBytesLang_verdictComponent A R
  have h₂ := exportRejected_verdictComponent A R
  unfold exportBytesLang at h₁
  unfold exportAcceptedNotRejected neverFalse
  rw [h₁, h₂]
  rfl

end Silmaril.Proofs.Wasi.Component.Accept
