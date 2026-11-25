module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Substitution.Defs

/-! # Encoding finite exit interfaces as a single sum type -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region

/-- A right-associated sum of the exit argument types. -/
@[expose] def packedExitType {τ : Type u} [TypeFormers τ] : LCtx τ → τ
  | [] => Silmaril.empty
  | A :: L => Silmaril.coprod A (packedExitType L)

/-- Inject a payload into its original label's position in the packed sum. -/
@[expose] def packedExitArg {Φ : Type v} : Nat → Tm Φ → Tm Φ
  | 0, a => .inl a
  | i + 1, a => .inr (packedExitArg i a)

/-- Redirect every outward edge to exit zero, tagging the payload with the
original exit's index. The native substitution lifts past local CFG labels. -/
@[expose] def packExits {Φ : Type v} (r : Region Φ) : Region Φ :=
  r.lsubst (fun i => .br 0 (packedExitArg i (.var 0)))

/-- Dispatch a packed exit, read from variable zero, to its original label.
The empty interface uses a loop on its impossible payload. -/
@[expose] def unpackExits {τ : Type u} {Φ : Type v} : LCtx τ → Region Φ
  | [] => .cfg (.br 0 (.var 0)) 1 (fun _ => .br 0 (.var 0))
  | _ :: L => .case (.var 0) (.br 0 (.var 0)) ((unpackExits L).renameLabels Nat.succ)

/-- The runtime tag corresponding to an exit's position in the packed sum. -/
@[expose] def packedExitValue {α : Type u} : Nat → Silmaril.Isotope.Value α → Silmaril.Isotope.Value α
  | 0, value => .inl value
  | i + 1, value => .inr (packedExitValue i value)

end Silmaril.Isotope.LambdaSSA.Region
