module

public import Silmaril.Logic.Smt.Defs
public import Silmaril.Logic.Inst.Builders.Core.Defs

/-!
# Institutions for the existing SMT script fragment

Whole scripts carry their declarations in the sentence. The signature category is a
singleton; this presentation does not implement symbol-renaming signatures. The abstract
script room and the accepted S-expression room share assignments as models. The decoder
corridor is exact and model-expansive.

This is precisely the fragment and evaluator of `Silmaril.Logic.Smt.Defs`, including its
documented division-by-zero choice. It is not the full SMT-LIB language or QF-UFLIA:
nonzero-arity uninterpreted functions are absent and `set-logic` is not enforced.
Malformed S-expressions are excluded from sentences, rather than called unsatisfiable.
-/

@[expose] public section

namespace Silmaril.Logic.Smt.Institution

open CategoryTheory Silmaril.Inst
open Silmaril.Logic.Institution (Room Corridor)

/-- An S-expression script together with its checked decoding. The equality is evidence
about the concrete syntax, not an assumption of satisfiability or unsatisfiability. -/
structure AcceptedForms where
  forms : List SE
  script : Script
  decoded : decodeScript forms = some script

/-- Direct S-expression semantics: successful decoding and script satisfaction. -/
def FormsHolds (forms : List SE) (ρ : Model) : Prop :=
  ∃ s, decodeScript forms = some s ∧ s.Holds ρ

/-- The room of abstract scripts, with declarations inside each sentence. -/
def scriptRoom : Room :=
  ⟨Script, Disc.cat Model, fun ρ s => s.Holds ρ⟩

/-- The room of accepted concrete S-expression scripts. -/
def formsRoom : Room :=
  ⟨AcceptedForms, Disc.cat Model, fun ρ s => FormsHolds s.forms ρ⟩

/-- Successful decoding identifies concrete and abstract satisfaction. -/
theorem formsHolds_iff (s : AcceptedForms) (ρ : Model) :
    FormsHolds s.forms ρ ↔ s.script.Holds ρ := by
  constructor
  · rintro ⟨t, ht, h⟩
    have heq : s.script = t := Option.some.inj (s.decoded.symm.trans ht)
    exact heq.symm ▸ h
  · intro h
    exact ⟨s.script, s.decoded, h⟩

/-- The decoder translates concrete sentences forward and leaves models unchanged. -/
def decodeCorridor : formsRoom ⟶ scriptRoom where
  sen := AcceptedForms.script
  mod := 𝟭 _
  sat ρ s := (formsHolds_iff s ρ).symm

/-- The singleton-signature abstract presentation. -/
def scriptPlain : Plain (Disc Unit) where
  Sen _ := Script
  map _ := id
  map_id _ _ := rfl
  map_comp _ _ _ := rfl
  Mod _ := Model
  reduct _ := id
  reduct_id _ _ := rfl
  reduct_comp _ _ _ := rfl
  Sat ρ s := s.Holds ρ
  sat_map _ _ _ := Iff.rfl

/-- The singleton-signature accepted concrete presentation. -/
def formsPlain : Plain (Disc Unit) where
  Sen _ := AcceptedForms
  map _ := id
  map_id _ _ := rfl
  map_comp _ _ _ := rfl
  Mod _ := Model
  reduct _ := id
  reduct_id _ _ := rfl
  reduct_comp _ _ _ := rfl
  Sat ρ s := FormsHolds s.forms ρ
  sat_map _ _ _ := Iff.rfl

abbrev scriptInst := scriptPlain.toInst
abbrev formsInst := formsPlain.toInst

/-- The exact decoder comorphism between the two whole-script institutions. -/
def decodeComorphism : Comorphism formsInst scriptInst :=
  Comorphism.ofPlain (𝟭 _) (fun _ => AcceptedForms.script) (fun _ => id)
    (fun _ ρ s => (formsHolds_iff s ρ).symm)
    (fun _ _ => rfl) (fun _ _ => rfl)

end Silmaril.Logic.Smt.Institution
