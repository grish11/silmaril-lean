module

public import Silmaril.Logic.CommonLogic.Source.Renaming.Defs

@[expose] public section
namespace Silmaril.Logic.CommonLogic.Source

@[simp] theorem find?_rename {α : Type} (r : Equiv.Perm String) (x : String)
    (entries : List (String × α)) :
    find? (r x) (entries.map (fun p => (r p.1, p.2))) = find? x entries := by
  induction entries with
  | nil => rfl
  | cons p ps ih =>
      simp only [List.map_cons, find?, beq_iff_eq, Equiv.apply_eq_iff_eq, ih]

/-- Valid class partitions and aliases survive simultaneous spelling renaming. -/
theorem Names.valid_rename {S : Core.Signature} (names : Names S)
    (r : Equiv.Perm String) (valid : names.Valid) : (names.rename r).Valid := by
  have keys {α : Type} (entries : List (String × α)) :
      ((entries.map (fun p => (r p.1, p.2))).map Prod.fst) =
        (entries.map Prod.fst).map r := by simp only [List.map_map, Function.comp_def]
  simp only [Names.Valid, Names.rename, keys]
  rcases valid with ⟨hd, hn, hm, hdn, hmd, hmn⟩
  refine ⟨List.Nodup.map r.injective hd, List.Nodup.map r.injective hn,
    List.Nodup.map r.injective hm, ?_, ?_, ?_⟩
  · intro x hD hN
    obtain ⟨d, hDmem, eqD⟩ := List.mem_map.mp hD
    obtain ⟨n, hNmem, eqN⟩ := List.mem_map.mp hN
    have same : n = d := r.injective (eqN.trans eqD.symm)
    exact hdn d hDmem (same ▸ hNmem)
  · intro x hM hD
    obtain ⟨m, hMmem, eqM⟩ := List.mem_map.mp hM
    obtain ⟨d, hDmem, eqD⟩ := List.mem_map.mp hD
    have same : d = m := r.injective (eqD.trans eqM.symm)
    exact hmd m hMmem (same ▸ hDmem)
  · intro x hM hN
    obtain ⟨m, hMmem, eqM⟩ := List.mem_map.mp hM
    obtain ⟨n, hNmem, eqN⟩ := List.mem_map.mp hN
    have same : n = m := r.injective (eqN.trans eqM.symm)
    exact hmn m hMmem (same ▸ hNmem)

@[simp] theorem renameEnv_apply {α : Type} (r : Equiv.Perm String)
    (ρ : String → Option α) (x : String) : renameEnv r ρ (r x) = ρ x := by
  simp only [renameEnv, Equiv.symm_apply_apply]

@[simp] theorem renameEnv_bind {α : Type} (r : Equiv.Perm String)
    (ρ : String → Option α) (x : String) (v : α) :
    bind (renameEnv r ρ) (r x) v = renameEnv r (bind ρ x v) := by
  funext y
  simp only [bind, renameEnv, beq_iff_eq, Equiv.symm_apply_eq]

/-- Capture safety is proved for arbitrary open environments, including repeated
binder spellings and independent individual/sequence scopes. -/
theorem Expr.eval_rename {S : Core.Signature} (names : Names S) (M : Core.Model S)
    (r : Equiv.Perm String) (ρ : String → Option M.Discourse)
    (σ : String → Option (List M.Discourse)) {a : Core.Kind} (t : Expr a) :
    (t.rename r).eval (names.rename r) M (renameEnv r ρ) (renameEnv r σ) =
      t.eval names M ρ σ := by
  induction t <;> simp_all [Expr.rename, Expr.eval, Names.rename]

theorem Formula.holds_rename {S : Core.Signature} (names : Names S) (M : Core.Model S)
    (r : Equiv.Perm String) (ρ : String → Option M.Discourse)
    (σ : String → Option (List M.Discourse)) (p : Formula) :
    (p.rename r).Holds (names.rename r) M (renameEnv r ρ) (renameEnv r σ) ↔
      p.Holds names M ρ σ := by
  induction p generalizing ρ σ <;>
    simp_all [Formula.rename, Formula.Holds, Expr.eval_rename, renameEnv_bind]

@[simp] theorem Expr.rename_refl {a : Core.Kind} (t : Expr a) :
    t.rename (Equiv.refl String) = t := by
  induction t <;> simp_all [rename]

@[simp] theorem Formula.rename_refl (p : Formula) :
    p.rename (Equiv.refl String) = p := by
  induction p <;> simp_all [rename, Expr.rename_refl]

theorem Expr.rename_trans (r s : Equiv.Perm String) {a : Core.Kind} (t : Expr a) :
    (t.rename r).rename s = t.rename (r.trans s) := by
  induction t <;> simp_all [rename]

theorem Formula.rename_trans (r s : Equiv.Perm String) (p : Formula) :
    (p.rename r).rename s = p.rename (r.trans s) := by
  induction p <;> simp_all [rename, Expr.rename_trans]

end Silmaril.Logic.CommonLogic.Source
