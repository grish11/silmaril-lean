module

public import Silmaril.Wasm.Abstract.InstSession.Defs

/-!
# Reading a session back on the instance interface: positions (proofs)

`srelabel` keeps the import moves and the export questions and changes only the export answers,
so positions of `E ↠ ifaceSig ts` correspond to positions of `E ↠ ssig ts` (`posS`), and a path
of a relabelled play is the image of a path of the play (`path_unmap`). Hence a play whose
relabelling is legal is legal (`legal_unmap`), keeps its running question (`run_unmap`), and
belongs to `spull` when its relabelling is a play (`mem_spull_of`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.InstSessionD

open Silmaril.Games
open Silmaril.Wasm.Game Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Abstract.InstSession

variable {E : Sig.{0}} {ts : List FnType}

/-- The same position, at the session interface. -/
def posS : Pos E (ifaceSig ts) → Pos E (ssig ts)
  | .idle => .idle
  | .run q => .run q
  | .wait q m => .wait q m

theorem step_unmap {x : Pos E (ifaceSig ts)} {o : Move E (ifaceSig ts)} {y' : Pos E (ssig ts)}
    (h : Step (posS x) (srelabel o) y') : ∃ y, Step x o y ∧ posS y = y' := by
  rcases x with _ | q | ⟨q, m⟩ <;> rcases o with (m' | ⟨m', n⟩) | (q' | ⟨q', r⟩) <;>
    simp only [posS, srelabel] at h <;> cases h
  all_goals exact ⟨_, by constructor, rfl⟩

theorem path_unmap {x : Pos E (ifaceSig ts)} {p : List (Move E (ifaceSig ts))}
    {y' : Pos E (ssig ts)} (h : Path (posS x) (p.map srelabel) y') :
    ∃ y, Path x p y ∧ posS y = y' := by
  induction p generalizing x with
  | nil =>
    simp only [List.map_nil] at h
    cases h
    exact ⟨x, .nil _, rfl⟩
  | cons o p ih =>
    rw [List.map_cons] at h
    cases h with
    | cons hs hp =>
      obtain ⟨z, hz, rfl⟩ := step_unmap hs
      obtain ⟨y, hy, rfl⟩ := ih hp
      exact ⟨y, .cons hz hy, rfl⟩

theorem legal_unmap {p : List (Move E (ifaceSig ts))} (h : Legal (p.map srelabel)) : Legal p := by
  obtain ⟨y', hy'⟩ := h
  obtain ⟨y, hy, -⟩ := path_unmap (x := .idle) hy'
  exact ⟨y, hy⟩

theorem run_unmap {p : List (Move E (ifaceSig ts))} {q : (ifaceSig ts).Op}
    (h : Path .idle (p.map srelabel) (Pos.run (E := E) (F := ssig ts) q)) :
    Path .idle p (.run q) := by
  obtain ⟨y, hy, he⟩ := path_unmap (x := .idle) h
  rcases y with _ | q' | ⟨q', m⟩ <;> simp only [posS, reduceCtorEq, Pos.run.injEq] at he
  exact he ▸ hy

theorem mem_spull_of {σ : Strategy E (ssig ts)} {p : List (Move E (ifaceSig ts))}
    (h : p.map srelabel ∈ σ) : p ∈ spull σ :=
  Strategy.subset_generate h (legal_unmap (σ.legal h))

end Silmaril.Proofs.Wasm.Abstract.InstSessionD
