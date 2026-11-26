module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Capture.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Input.Destructure.InstructionMap.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Capture

open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.Bridge.NamedFlat
open Silmaril.Isotope.Bridge.NamedFlat.Capture

universe u v w

variable {Φ : Type u} {Ψ : Type v} (f : Φ → Ψ)

private theorem scoped_map (t : Tm Φ) (n : Nat) : (t.mapInstr f).Scoped n ↔ t.Scoped n := by
  induction t generalizing n <;> simp_all [Tm.Scoped, Tm.mapInstr]

private theorem decode_map (t : Tm Φ) (n : Nat) :
    Morphism.CaseSSA.decode? n (t.mapInstr f) =
      (Morphism.CaseSSA.decode? n t).map (fun a => a.mapInstr f) := by
  cases h : Morphism.CaseSSA.decode? n t with
  | none =>
    have hs : ¬ t.Scoped n := fun hscope => by simp [Morphism.CaseSSA.decode?, hscope] at h
    simp [Morphism.CaseSSA.decode?, scoped_map, hs]
  | some a =>
    rw [← Morphism.CaseSSA.decode?_eq_some_iff.mp h, ← Morphism.CaseSSA.erase_mapInstr]
    simp only [Morphism.CaseSSA.decode?_erase, Option.map_some]

private theorem reify_map {labels n : Nat} (r : Region Φ) :
    (reify (r.mapInstr f) : Option (Flat Ψ labels n)) =
      (reify r : Option (Flat Φ labels n)).map (Flat.mapInstr f) := by
  induction r generalizing n with
  | br i a =>
    by_cases hi : i < labels
    · cases h : Morphism.CaseSSA.decode? n a <;> simp [reify, Region.mapInstr, decode_map, hi, h, Flat.mapInstr]
    · simp [reify, Region.mapInstr, hi]
  | let₁ a r ih =>
    cases h : Morphism.CaseSSA.decode? n a <;>
      simp [reify, Region.mapInstr, decode_map, h, ih, Flat.mapInstr, Option.map_map, Function.comp_def]
  | let₂ a r ih =>
    cases h : Morphism.CaseSSA.decode? n a <;>
      simp [reify, Region.mapInstr, decode_map, h, ih, Flat.mapInstr, Option.map_map, Function.comp_def]
  | case a l r ihl ihr =>
    cases h : Morphism.CaseSSA.decode? n a <;>
      cases hl : (reify l : Option (Flat Φ labels (n + 1))) <;>
      simp [reify, Region.mapInstr, decode_map, h, hl, ihl, ihr, Flat.mapInstr,
        Option.map_map, Function.comp_def]
  | cfg => rfl

private theorem tabulate_map {α : Type u} {β : Type v} (map : α → β) (n : Nat)
    (xs : Fin n → Option α) :
    tabulate n (fun i => (xs i).map map) =
      (tabulate n xs).map (fun ys i => map (ys i)) := by
  induction n with
  | zero =>
    simp only [tabulate, Option.map_some]
    exact congrArg some (funext (fun i => Fin.elim0 i))
  | succ n ih =>
    simp only [tabulate, ih]
    cases head : xs 0 with
    | none => rfl
    | some val =>
      cases tail : tabulate n (fun i => xs i.succ) with
      | none => rfl
      | some rest =>
        simp only [Option.map_some, Option.bind_some]
        exact congrArg some (funext (Fin.cases rfl (fun _ => rfl)))

variable {τ : Type w} {blocks exits n : Nat} {β : BoundCtx τ n}
  {g : FiniteCFG Φ blocks exits n} {closed : FiniteCFG Φ blocks exits 0}
  {input : LetCase.LocallyNameless.Tm Empty Φ 0}

theorem closes_mapInstr (h : Closes β input g closed) :
    Closes β (input.mapInstr f) (g.mapInstr f) (closed.mapInstr f) := by
  constructor
  · simp only [FiniteCFG.mapInstr, Flat.erase_mapInstr, h.entry, Region.mapInstr,
      Region.packInputsDestructure_mapInstr, Morphism.CaseSSA.erase_mapInstr]
  · intro i
    simp only [FiniteCFG.mapInstr, Flat.erase_mapInstr, h.block i]

section Checker

variable {Base : Type w} [DecidableEq Base] [HasTy Φ (Ty Base)] [HasTy Ψ (Ty Base)]
  (profiles : InstructionMap.PreservesTypes (τ := Ty Base) f)

include profiles

private theorem infer_map {n : Nat} (β : BoundCtx (Ty Base) n)
    (a : LetCase.LocallyNameless.Tm Empty Φ n) : infer β (a.mapInstr f) = infer β a := by
  induction a <;> simp_all [infer, LetCase.LocallyNameless.Tm.mapInstr, profiles.source, profiles.target]

private theorem checkBody_map {labels n : Nat} (types : Fin labels → Ty Base)
    (β : BoundCtx (Ty Base) n) (body : Flat Φ labels n) :
    checkBody types β (body.mapInstr f) = checkBody types β body := by
  induction body <;> simp_all [checkBody, Flat.mapInstr, infer_map f profiles]

omit profiles [HasTy Ψ (Ty Base)] in
private theorem close_value (β : BoundCtx (Ty Base) n) (R : Fin blocks → Ty Base)
    (L : Fin exits → Ty Base) (g : FiniteCFG Φ blocks exits n) (hg : g.HasType β R L)
    (input : LetCase.LocallyNameless.Tm Empty Φ 0)
    (typed : LetCase.LocallyNameless.HasType Φ .nil .nil input (Region.packedInputType β.toList)) :
    (close β R L g hg input typed).map Subtype.val = (do
      let entry ← reify (g.entry.erase.packInputsDestructure β.toList)
      let table ← tabulate blocks (fun i => reify (g.block i).erase)
      if (List.finRange blocks).all
          (fun i => checkBody (SSA.FiniteSum.append R L) (.snoc .nil (R i)) (table i)) = true then
        some ⟨.let₁ input entry, table⟩
      else none) := by
  unfold close
  split
  · rename_i h
    simp [h]
  · rename_i entry he
    simp only [he]
    split
    · rename_i h
      simp [h]
    · rename_i table hb
      simp only [hb]
      change _ =
        (if (List.finRange blocks).all (fun i =>
            checkBody (SSA.FiniteSum.append R L) (.snoc .nil (R i)) (table i)) = true then
          some (⟨.let₁ input entry, table⟩ : FiniteCFG Φ blocks exits 0) else none)
      split <;> rfl

theorem close_mapInstr (β : BoundCtx (Ty Base) n) (R : Fin blocks → Ty Base) (L : Fin exits → Ty Base)
    (g : FiniteCFG Φ blocks exits n) (hg : g.HasType β R L)
    (input : LetCase.LocallyNameless.Tm Empty Φ 0)
    (typed : LetCase.LocallyNameless.HasType Φ .nil .nil input (Region.packedInputType β.toList))
    (mapped : LetCase.LocallyNameless.HasType Ψ .nil .nil (input.mapInstr f)
      (Region.packedInputType β.toList)) :
    (close β R L (g.mapInstr f) (hg.mapInstr profiles) (input.mapInstr f) mapped).map Subtype.val =
      (close β R L g hg input typed).map (fun out => out.val.mapInstr f) := by
  have entry :
      (reify ((g.mapInstr f).entry.erase.packInputsDestructure β.toList) :
        Option (Flat Ψ (blocks + exits) 1)) =
      (reify (g.entry.erase.packInputsDestructure β.toList) :
        Option (Flat Φ (blocks + exits) 1)).map (Flat.mapInstr f) := by
    simp only [FiniteCFG.mapInstr, Flat.erase_mapInstr, ← Region.packInputsDestructure_mapInstr, reify_map]
  have table :
      (tabulate blocks (fun i => reify ((g.mapInstr f).block i).erase) :
        Option (Fin blocks → Flat Ψ (blocks + exits) 1)) =
      (tabulate blocks (fun i => reify (g.block i).erase) :
        Option (Fin blocks → Flat Φ (blocks + exits) 1)).map (fun bs i => (bs i).mapInstr f) := by
    simp only [FiniteCFG.mapInstr, Flat.erase_mapInstr, reify_map, tabulate_map]
  have source := congrArg (Option.map (FiniteCFG.mapInstr f)) (close_value β R L g hg input typed)
  simp only [Option.map_map, Function.comp_def] at source
  rw [source, close_value, entry, table]
  cases he : (reify (g.entry.erase.packInputsDestructure β.toList) :
      Option (Flat Φ (blocks + exits) 1)) with
  | none => rfl
  | some e =>
    cases hb : (tabulate blocks (fun i => reify (g.block i).erase) :
        Option (Fin blocks → Flat Φ (blocks + exits) 1)) with
    | none => rfl
    | some bs =>
      change
        (if (List.finRange blocks).all (fun i =>
            checkBody (SSA.FiniteSum.append R L) (.snoc .nil (R i)) ((bs i).mapInstr f)) = true then
          some ⟨.let₁ (input.mapInstr f) (e.mapInstr f), fun i => (bs i).mapInstr f⟩ else none) =
        (if (List.finRange blocks).all (fun i =>
            checkBody (SSA.FiniteSum.append R L) (.snoc .nil (R i)) (bs i)) = true then
          some ⟨.let₁ input e, bs⟩ else none).map (FiniteCFG.mapInstr f)
      simp only [checkBody_map f profiles]
      split <;> rfl

end Checker
end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Capture
