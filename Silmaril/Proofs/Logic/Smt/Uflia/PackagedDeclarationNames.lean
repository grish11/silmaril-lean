module

public import Silmaril.Logic.Smt.Uflia.Packaged.Defs
public import Mathlib.Data.List.Nodup

@[expose] public section

namespace Silmaril.Proofs.Logic.Smt.Uflia.PackagedDeclarationNames

open Silmaril.Logic.Smt.Uflia Silmaril.Logic.Smt.Uflia.Packaged
open Silmaril.Logic.Smt.Uflia.SExpr

private def symbolIndex {E : Environment} {n inputs output}
    (symbol : Symbol E n inputs output) : Fin E.declarations.length :=
  match symbol with
  | .declared i => i

private theorem symbol_heq_of_index_eq {E : Environment} {n inputs output n' inputs' output'}
    (a : Symbol E n inputs output) (b : Symbol E n' inputs' output')
    (h : symbolIndex a = symbolIndex b) : HEq a b := by
  cases a with
  | declared i =>
    cases b with
    | declared j =>
      change i = j at h
      cases h
      rfl

private theorem nameMap_index {E : Environment} {n inputs output}
    (symbol : Symbol E n inputs output) :
    (nameMap E).operations symbol = (E.declarations.get (symbolIndex symbol)).name := by
  cases symbol
  rfl

/-- A finite, syntactic uniqueness condition suffices for model expansion.
It is stronger than per-profile uniqueness and mentions no semantic result. -/
theorem namesInjective_of_declarationNames (E : Environment)
    (h : Function.Injective (fun i : Fin E.declarations.length =>
      (E.declarations.get i).name)) : NamesInjective E := by
  intro n inputs output a b hab
  apply eq_of_heq
  apply symbol_heq_of_index_eq
  apply h
  exact (nameMap_index a).symm.trans (hab.trans (nameMap_index b))

private theorem addDeclaration_names_nodup {E E' : Environment} {name inputs output}
    (hN : (E.declarations.map Declaration.name).Nodup)
    (h : E.addDeclaration? name inputs output = some E') :
    (E'.declarations.map Declaration.name).Nodup := by
  unfold Environment.addDeclaration? at h
  split at h
  · rename_i hc
    cases h
    have hfresh : E.declarations.any (fun d => d.name == name) = false :=
      by simpa using (Bool.and_eq_true_iff.mp hc).2
    have hnot : name ∉ E.declarations.map Declaration.name := by
      intro hm
      obtain ⟨d, hd, heq⟩ := List.mem_map.mp hm
      exact (List.any_eq_false.mp hfresh d hd) (by simp [heq])
    simp only [List.map_append, List.map_cons, List.map_nil]
    exact hN.append (by simp) (by simpa using hnot)
  · contradiction

private theorem command_names_nodup {E E' : Environment} (e : Expr)
    (hN : (E.declarations.map Declaration.name).Nodup)
    (h : E.command? e = some E') : (E'.declarations.map Declaration.name).Nodup := by
  unfold Environment.command? at h
  split at h
  · split at h
    · cases h
      exact hN
    · contradiction
  · change Option.bind _ _ = some E' at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨result, _, hAdd⟩ := h
    exact addDeclaration_names_nodup hN hAdd
  · change Option.bind _ _ = some E' at h
    obtain ⟨arguments, _, h⟩ := Option.bind_eq_some_iff.mp h
    change Option.bind _ _ = some E' at h
    obtain ⟨result, _, hAdd⟩ := Option.bind_eq_some_iff.mp h
    exact addDeclaration_names_nodup hN hAdd
  · contradiction

private theorem fold_commands_names_nodup (forms : List Expr) {E E' : Environment}
    (hN : (E.declarations.map Declaration.name).Nodup)
    (h : forms.foldlM Environment.command? E = some E') :
    (E'.declarations.map Declaration.name).Nodup := by
  induction forms generalizing E with
  | nil =>
    change some E = some E' at h
    cases h
    exact hN
  | cons e forms ih =>
    rw [List.foldlM_cons] at h
    change Option.bind _ _ = some E' at h
    obtain ⟨next, hNext, hTail⟩ := Option.bind_eq_some_iff.mp h
    exact ih (command_names_nodup e hN hNext) hTail

/-- Successful decoding enforces globally unique declaration names. -/
theorem checked_declarationNames_nodup (checked : DeclarationPrefix) :
    (checked.environment.declarations.map Declaration.name).Nodup :=
  fold_commands_names_nodup checked.forms (by simp) checked.decoded

/-- The checked declaration prefix supplies the required structural hypothesis;
no solver answer or model property is assumed. -/
theorem checked_namesInjective (checked : DeclarationPrefix) :
    NamesInjective checked.environment := by
  apply namesInjective_of_declarationNames
  intro i j h
  have hn := checked_declarationNames_nodup checked
  have heq : (checked.environment.declarations.map Declaration.name).get
      ⟨i.val, by simp⟩ =
      (checked.environment.declarations.map Declaration.name).get
      ⟨j.val, by simp⟩ := by
    simpa using h
  have hij := hn.injective_get heq
  exact Fin.ext (congrArg (fun k : Fin
    (checked.environment.declarations.map Declaration.name).length => k.val) hij)

end Silmaril.Proofs.Logic.Smt.Uflia.PackagedDeclarationNames
