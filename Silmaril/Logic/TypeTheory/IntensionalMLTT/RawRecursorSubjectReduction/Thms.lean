module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.RawValueGeneration.Thms
public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Computation
import Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRecursorSubjectReduction

public section

/-!
# Original Nat/J root subject reduction at the requested carrier

These theorems start with arbitrary original typing trees of the redex,
including trees ending in conversion and cumulativity. Their contracta retain
the exact requested source carrier. The successor case recovers actual
predecessor typing by constructor generation. The existing exact based-J
rule is retained. Beta/projection and compatible contextual subject reduction
remain separate; no original component injectivity is assumed.
-/

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT

/-- Original Nat-zero contraction preserves the requested carrier through any typing tree. -/
theorem Derivation.nat_zero_subjectReduction {n : ℕ} {Γ : Context n} {T z s : Term n} {C : Term (n + 1)}
    (h : Derivation Γ (.natrec C z s .zero) T) : Typing Γ z T :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRecursorSubjectReduction.nat_zero_subjectReduction h

/-- Original Nat-successor contraction preserves the requested carrier and genuine recursive call. -/
theorem Derivation.nat_succ_subjectReduction {n : ℕ} {Γ : Context n} {T z s t : Term n} {C : Term (n + 1)}
    (h : Derivation Γ (.natrec C z s (.succ t)) T) :
    Typing Γ (.app (.app s t) (.natrec C z s t)) T :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRecursorSubjectReduction.nat_succ_subjectReduction h

/-- The original exact based-J contraction preserves the requested carrier through any typing tree. -/
theorem Derivation.j_refl_subjectReduction {n : ℕ} {Γ : Context n} {T A a d : Term n} {C : Term (n + 2)}
    (h : Derivation Γ (.j A a C d a (.refl a)) T) : Typing Γ d T :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRecursorSubjectReduction.j_refl_subjectReduction h

/-- Arbitrary original Nat-zero typing gives typed equality at its requested carrier. -/
theorem TypedEq.nat_zero_of_typing {n : ℕ} {Γ : Context n} {T z s : Term n} {C : Term (n + 1)}
    (h : Typing Γ (.natrec C z s .zero) T) : TypedEq Γ (.natrec C z s .zero) z T := by
  obtain ⟨ht⟩ := h
  exact ⟨⟨ht⟩, ht.nat_zero_subjectReduction, ⟨.nat_zero C z s⟩⟩

/-- Arbitrary original Nat-successor typing gives typed equality at its requested carrier. -/
theorem TypedEq.nat_succ_of_typing {n : ℕ} {Γ : Context n} {T z s t : Term n} {C : Term (n + 1)}
    (h : Typing Γ (.natrec C z s (.succ t)) T) :
    TypedEq Γ (.natrec C z s (.succ t)) (.app (.app s t) (.natrec C z s t)) T := by
  obtain ⟨ht⟩ := h
  exact ⟨⟨ht⟩, ht.nat_succ_subjectReduction, ⟨.nat_succ C z s t⟩⟩

/-- Arbitrary original exact-J typing gives typed equality at its requested carrier. -/
theorem TypedEq.j_refl_of_typing {n : ℕ} {Γ : Context n} {T A a d : Term n} {C : Term (n + 2)}
    (h : Typing Γ (.j A a C d a (.refl a)) T) : TypedEq Γ (.j A a C d a (.refl a)) d T := by
  obtain ⟨ht⟩ := h
  exact ⟨⟨ht⟩, ht.j_refl_subjectReduction, ⟨.j_refl A a C d⟩⟩

end Silmaril.Logic.TypeTheory.IntensionalMLTT
