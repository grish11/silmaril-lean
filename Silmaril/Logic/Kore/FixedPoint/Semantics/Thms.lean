module

public import Silmaril.Proofs.Logic.Kore.FixedPoint.Adequacy

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.FixedPoint.Semantics
export Silmaril.Proofs.Logic.Kore.FixedPoint (elaborate_sound)
variable {scope : Modules.Scope} (M : Matching.FixedPoint.Model scope.signature)

/-- Complete-text adequacy, retaining actual parsing and symbol resolution. -/
theorem read_sound (fuel : Nat) (sets objects : Names) (s text : String)
    (typed : Pattern scope sets objects s)
    (v : ∀ i, M.carrier (context objects i))
    (η : ∀ i, Set (M.carrier (context sets i)))
    (accepted : Checking.read scope fuel sets objects s text = some typed) :
    read scope M fuel (interpret M sets η) (interpret M objects (fun i => {v i})) s text =
      some (typed.denote M v η) := by
  cases parsed : Syntax.parse text with
  | none => simp [Checking.read, parsed] at accepted
  | some raw =>
      simp only [Checking.read, parsed, bind, Option.bind] at accepted
      simpa only [read, parsed, bind, Option.bind] using
        elaborate_sound M fuel sets objects s raw typed v η accepted

/-- Successful checking supplies actual monotonicity of the independent raw
meaning. Unsupported raw inputs receive no such claim. -/
theorem accepted_monotone (fuel : Nat) (sets objects : Names) (s : String)
    (raw : RawPattern) (typed : Pattern scope sets objects s)
    (accepted : Checking.elaborate scope fuel sets objects s raw = some typed)
    (v : ∀ i, M.carrier (context objects i))
    {η ζ : ∀ i, Set (M.carrier (context sets i))} (h : η ≤ ζ) :
    (denote scope M fuel (interpret M sets η) (interpret M objects (fun i => {v i})) s raw).getD ∅ ⊆
      (denote scope M fuel (interpret M sets ζ) (interpret M objects (fun i => {v i})) s raw).getD ∅ := by
  rw [elaborate_sound M fuel sets objects s raw typed v η accepted,
    elaborate_sound M fuel sets objects s raw typed v ζ accepted]
  exact (typed.denote M v).monotone h

/-- Closed raw satisfaction is exactly native satisfaction at every carrier
point after successful checking, with no model constraints beyond the target. -/
theorem closed_satisfies (fuel : Nat) (s : String) (raw : RawPattern)
    (typed : Pattern scope [] [] s)
    (accepted : Checking.elaborate scope fuel [] [] s raw = some typed) :
    (∀ x, x ∈ (denote scope M fuel [] [] s raw).getD ∅) ↔
      ∀ x, x ∈ typed.denote M (fun i => i.elim0) (fun i => i.elim0) := by
  have meaning := elaborate_sound M fuel [] [] s raw typed
    (fun i => i.elim0) (fun i => i.elim0) accepted
  simp only [interpret] at meaning
  rw [meaning]
  rfl
end Silmaril.Logic.Kore.FixedPoint.Semantics
