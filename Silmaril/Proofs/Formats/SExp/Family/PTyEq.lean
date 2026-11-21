module

public import Silmaril.Formats.SExp.Family.Defs

/-!
# Proofs: boolean equality of payload types

`eq_of_beq` (with `eq_of_beqList`, `eq_of_beqFields`, `eq_of_beqCases`, `eq_of_beqOpt`) and
`beq_self` (with its list, field, case and option forms): `PTy.beq` is equality, so
`DecidableEq PTy` (`Silmaril.Formats.SExp.Family.Thms`).

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Formats.SExp.Family

open Silmaril.Formats

mutual
theorem eq_of_beq : ∀ {a b : PTy}, PTy.beq a b = true → a = b
  | .bool, b, h | .s32, b, h | .u32, b, h | .s64, b, h | .u64, b, h | .string, b, h
  | .s8, b, h | .u8, b, h | .s16, b, h | .u16, b, h | .f32, b, h | .f64, b, h
  | .char, b, h => by cases b <;> simp_all [PTy.beq]
  | .list a, b, h => by
    cases b <;> simp [PTy.beq] at h
    exact congrArg PTy.list (eq_of_beq h)
  | .option a, b, h => by
    cases b <;> simp [PTy.beq] at h
    exact congrArg PTy.option (eq_of_beq h)
  | .fixedList a n, b, h => by
    cases b <;> simp [PTy.beq] at h
    obtain ⟨h₁, rfl⟩ := h
    rw [eq_of_beq h₁]
  | .record fs, b, h => by
    cases b <;> simp [PTy.beq] at h
    exact congrArg PTy.record (eq_of_beqFields h)
  | .tuple ts, b, h => by
    cases b <;> simp [PTy.beq] at h
    exact congrArg PTy.tuple (eq_of_beqList h)
  | .variant cs, b, h => by
    cases b <;> simp [PTy.beq] at h
    exact congrArg PTy.variant (eq_of_beqCases h)
  | .enum cs, b, h => by cases b <;> simp_all [PTy.beq]
  | .flags ls, b, h => by cases b <;> simp_all [PTy.beq]
  | .own r, b, h => by cases b <;> simp_all [PTy.beq]
  | .borrow r, b, h => by cases b <;> simp_all [PTy.beq]
  | .result a c, b, h => by
    cases b <;> simp [PTy.beq] at h
    obtain ⟨h₁, h₂⟩ := h
    rw [eq_of_beqOpt h₁, eq_of_beqOpt h₂]

theorem eq_of_beqList : ∀ {as bs : List PTy}, PTy.beqList as bs = true → as = bs
  | [], bs, h => by cases bs <;> simp_all [PTy.beqList]
  | a :: as, bs, h => by
    cases bs <;> simp [PTy.beqList] at h
    obtain ⟨h₁, h₂⟩ := h
    rw [eq_of_beq h₁, eq_of_beqList h₂]

theorem eq_of_beqFields : ∀ {as bs : List (String × PTy)}, PTy.beqFields as bs = true → as = bs
  | [], bs, h => by cases bs <;> simp_all [PTy.beqFields]
  | (n, a) :: as, bs, h => by
    rcases bs with _ | ⟨⟨m, b⟩, bs⟩ <;> simp [PTy.beqFields] at h
    obtain ⟨⟨rfl, h₁⟩, h₂⟩ := h
    rw [eq_of_beq h₁, eq_of_beqFields h₂]

theorem eq_of_beqCases :
    ∀ {as bs : List (String × Option PTy)}, PTy.beqCases as bs = true → as = bs
  | [], bs, h => by cases bs <;> simp_all [PTy.beqCases]
  | (n, a) :: as, bs, h => by
    rcases bs with _ | ⟨⟨m, b⟩, bs⟩ <;> simp [PTy.beqCases] at h
    obtain ⟨⟨rfl, h₁⟩, h₂⟩ := h
    rw [eq_of_beqOpt h₁, eq_of_beqCases h₂]

theorem eq_of_beqOpt : ∀ {a b : Option PTy}, PTy.beqOpt a b = true → a = b
  | none, b, h => by cases b <;> simp_all [PTy.beqOpt]
  | some a, b, h => by
    cases b <;> simp [PTy.beqOpt] at h
    exact congrArg some (eq_of_beq h)
end

mutual
theorem beq_self : ∀ a : PTy, PTy.beq a a = true
  | .bool | .s32 | .u32 | .s64 | .u64 | .string | .s8 | .u8 | .s16 | .u16 | .f32 | .f64
  | .char | .enum _ | .flags _ | .own _ | .borrow _ => by simp [PTy.beq]
  | .list a | .option a => by simp [PTy.beq, beq_self a]
  | .fixedList a _ => by simp [PTy.beq, beq_self a]
  | .record fs => by simp [PTy.beq, beqFields_self fs]
  | .tuple ts => by simp [PTy.beq, beqList_self ts]
  | .variant cs => by simp [PTy.beq, beqCases_self cs]
  | .result a b => by simp [PTy.beq, beqOpt_self a, beqOpt_self b]

theorem beqList_self : ∀ as : List PTy, PTy.beqList as as = true
  | [] => by simp [PTy.beqList]
  | a :: as => by simp [PTy.beqList, beq_self a, beqList_self as]

theorem beqFields_self : ∀ as : List (String × PTy), PTy.beqFields as as = true
  | [] => by simp [PTy.beqFields]
  | (_, a) :: as => by simp [PTy.beqFields, beq_self a, beqFields_self as]

theorem beqCases_self : ∀ as : List (String × Option PTy), PTy.beqCases as as = true
  | [] => by simp [PTy.beqCases]
  | (_, a) :: as => by simp [PTy.beqCases, beqOpt_self a, beqCases_self as]

theorem beqOpt_self : ∀ a : Option PTy, PTy.beqOpt a a = true
  | none => by simp [PTy.beqOpt]
  | some a => by simp [PTy.beqOpt, beq_self a]
end

theorem beq_iff (a b : PTy) : PTy.beq a b = true ↔ a = b :=
  ⟨eq_of_beq, fun h => h ▸ beq_self a⟩

end Silmaril.Proofs.Formats.SExp.Family
