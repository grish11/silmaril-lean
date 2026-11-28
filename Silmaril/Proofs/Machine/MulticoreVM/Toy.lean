module

public import Silmaril.Machine.MulticoreVM.Toy.Defs

public section

namespace Silmaril.Proofs.Machine.MulticoreVM

open Silmaril.Machine.MulticoreVM
open Silmaril.Machine.MulticoreVM.Toy
open Silmaril.Semantics.ConcurrentTrace (Equivalent ofWord_eq_iff swap)

private theorem put_comm (cfg : Config) {a b : ThreadId} (distinct : a ≠ b) (c d : Core) :
    put (put cfg a c) b d = put (put cfg b d) a c := by
  funext t
  by_cases atA : t = a
  · subst t
    simp [put, distinct]
  · simp [put, atA]

theorem emit_commutes (cfg : Config) {a b : ThreadId} (distinct : a ≠ b)
    {x y : Nat} {p q : List Instr}
    (atA : cfg a = some ⟨x, .emit :: p⟩) (atB : cfg b = some ⟨y, .emit :: q⟩) :
    ∃ final,
      execute exec [⟨a, none⟩, ⟨b, none⟩] cfg = some (final, [.event a x, .event b y]) ∧
      execute exec [⟨b, none⟩, ⟨a, none⟩] cfg = some (final, [.event b y, .event a x]) ∧
      Equivalent [.event a x, .event b y] [.event b y, .event a x] := by
  refine ⟨put (put cfg a ⟨x, p⟩) b ⟨y, q⟩, ?_, ?_, (ofWord_eq_iff _ _).mp (swap (.events distinct))⟩
  · simp [execute, exec, atA, atB, put, Ne.symm distinct, nameFragment]
  · rw [put_comm cfg distinct]
    simp [execute, exec, atA, atB, put, distinct, nameFragment]

end Silmaril.Proofs.Machine.MulticoreVM
