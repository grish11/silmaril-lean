module

public import Silmaril.Wasi.Component.Accept.Thms

/-!
# Specification components accept exactly their languages: proofs

`importAcceptor L run` and `exportAcceptor L` are generated strategies. Acceptance observes
Proponent moves only (an import call, an export answer), so it is read off the generating
plays (`Strategy.accepted_generate`); each generating play is legal and carries exactly one
observed move, whose argument `bytesVal w` decodes back to `w` (`bytes?_bytesV_toBitVec`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasi.Component.Accept

open Silmaril.Games Silmaril.Games.Accept Silmaril.Formats.Accept Silmaril.Wasi
  Silmaril.Wasi.Accept
open Silmaril.Wasm.Component (Val)

variable {α : Type} {f : FnName} {dec : List Val → Option α}

/-- Import calls are Proponent moves. -/
theorem importObs_not_isO {I X : Set FnName} (m : Move (nsig I) (nsig X)) (a : α)
    (h : (importObs f dec ∘ wev) m = some a) : ¬ m.IsO := by
  rcases m with (_ | _) | (_ | _) <;> simp_all [importObs, wev, Move.IsO]

/-- Export answers are Proponent moves. -/
theorem exportObs_not_isO {I X : Set FnName} (m : Move (nsig I) (nsig X)) (a : α)
    (h : (exportObs f dec ∘ wev) m = some a) : ¬ m.IsO := by
  rcases m with (_ | _) | (_ | _) <;> simp_all [exportObs, wev, Move.IsO]

theorem bytesLang_importAcceptor (L : ByteLang) (run : FnName) :
    bytesLang (importAcceptor L run) = L := by
  change importAccepted (importAcceptor L run) acceptFn (args1 bytes?) = (L : Set (List UInt8))
  rw [importAccepted_eq, importAcceptor, Strategy.accepted_generate importObs_not_isO]
  ext w
  constructor
  · rintro ⟨s, ⟨⟨w', hw', rfl⟩, -⟩, m, hm, ho⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · simp [importObs, wev] at ho
    · simp only [Function.comp_apply, wev, importObs, ite_true, args1, bytesVal,
        bytes?_bytesV_toBitVec, Option.some.injEq] at ho
      exact ho ▸ hw'
  · intro hw
    refine ⟨_, ⟨⟨w, hw, rfl⟩, ⟨_, .cons (.ask _) (.cons (.call _ _) (.nil _))⟩⟩, _,
      List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    simp only [Function.comp_apply, wev, importObs, ite_true, args1, bytesVal,
      bytes?_bytesV_toBitVec]

theorem exportBytesLang_exportAcceptor (L : ByteLang) :
    exportBytesLang (exportAcceptor L) = L := by
  change exportAccepted (exportAcceptor L) acceptFn (args1 bytes?) = (L : Set (List UInt8))
  rw [exportAccepted_eq, exportAcceptor, Strategy.accepted_generate exportObs_not_isO]
  ext w
  constructor
  · rintro ⟨s, ⟨⟨w', hw', rfl⟩, -⟩, m, hm, ho⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · simp [exportObs, wev] at ho
    · simp only [Function.comp_apply, wev, exportObs, ite_true, args1, bytesVal,
        bytes?_bytesV_toBitVec, Option.some.injEq] at ho
      exact ho ▸ hw'
  · intro hw
    refine ⟨_, ⟨⟨w, hw, rfl⟩, ⟨_, .cons (.ask _) (.cons (.ret _ _) (.nil _))⟩⟩, _,
      List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    simp only [Function.comp_apply, wev, exportObs, ite_true, args1, bytesVal,
      bytes?_bytesV_toBitVec]

end Silmaril.Proofs.Wasi.Component.Accept
