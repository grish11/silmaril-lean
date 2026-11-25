module

public import Silmaril.Wasm.Institution.Operational.LegacyDivision.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.LegacyDivision.Induction

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.LegacyDivision

open Silmaril.Semantics.SOS Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Runtime

variable {I : Type} {S : Syntax I}

@[simp] theorem admitted_nil : Admitted S [] := fun _ h => nomatch h

@[simp] theorem admitted_cons {a : AdminInstr I} {code : List (AdminInstr I)} :
    Admitted S (a :: code) ↔ Allowed S a ∧ Admitted S code := by simp [Admitted]

@[simp] theorem admitted_append {a b : List (AdminInstr I)} :
    Admitted S (a ++ b) ↔ Admitted S a ∧ Admitted S b := List.forall_mem_append

@[simp] theorem admitted_values (vs : List Value) : Admitted S (S.values vs) := by
  intro a h
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp h
  exact .value v

@[simp] theorem allowed_value (v : Value) : Allowed S (S.value v) := .value v
@[simp] theorem allowed_divide (t : IntType) (sign : Signedness) :
    Allowed S (S.divide t sign) := .divide t sign
@[simp] theorem allowed_nop : Allowed S S.nop := .nop
@[simp] theorem allowed_trap : Allowed S .trap := .trap

theorem derives_redex {before after : List (AdminInstr I)}
    (h : Redex S before after) : DerivesEdge S before after :=
  Derives.apply (R := (presentation S).rules) (r := ⟨[], (before, after)⟩)
    (.redex h) (fun _ h => nomatch h)

theorem derives_context {before after tail : List (AdminInstr I)} (saved : List Value)
    (h : DerivesEdge S before after) (tailOk : Admitted S tail) :
    DerivesEdge S (S.values saved ++ before ++ tail) (S.values saved ++ after ++ tail) :=
  Derives.apply (R := (presentation S).rules) (r := ⟨[(before, after)], _, _⟩)
    (.context saved before after tail tailOk) (fun _ hmem => (List.mem_singleton.mp hmem).symm ▸ h)

theorem Redex.admitted {before after : List (AdminInstr I)} (h : Redex S before after) :
    Admitted S before ∧ Admitted S after := by
  cases h <;> simp_all

theorem derives_induction {R : List (AdminInstr I) → List (AdminInstr I) → Prop}
    (redex : ∀ {before after}, Redex S before after → R before after)
    (context : ∀ saved {before after tail}, R before after → Admitted S tail →
      R (S.values saved ++ before ++ tail) (S.values saved ++ after ++ tail))
    {before after : List (AdminInstr I)} (h : DerivesEdge S before after) : R before after :=
  Proofs.derives_induction redex context h

theorem derives_admitted {before after : List (AdminInstr I)} (h : DerivesEdge S before after) :
    Admitted S before ∧ Admitted S after :=
  derives_induction Redex.admitted (fun _ {_ _ _} inner tailOk => by simpa [tailOk] using inner) h

theorem path_admitted {before after : List (AdminInstr I)} (h : DerivesPath S before after)
    (admitted : Admitted S before) : Admitted S after := by
  cases h with
  | refl => exact admitted
  | tail _ step => exact (derives_admitted step).2

end Silmaril.Wasm.Institution.Operational.LegacyDivision
