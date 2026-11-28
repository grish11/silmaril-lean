module

public import Silmaril.Elf.Corpus.SqliteMutex.Unlock.EagerBinding.Defs
import Silmaril.Elf.Corpus.SqliteMutex.Unlock.EagerBinding.Thms
import Silmaril.Elf.Link.Dyn.Elf.Thms

public section

namespace Silmaril.Proofs.Elf.Corpus.SqliteMutex.Unlock.SlotTable

open Silmaril.Elf.Link
open Silmaril.Elf.Link.DynElf
open Silmaril.Elf.Corpus.SqliteMutex.Unlock.EagerBinding

local notation "Sqlite" => Silmaril.Elf.Staged.Corpus.Sqlite.X8664.Libsqlite3So.F

private theorem run_mapM {α β : Type} (oracle : Nat → Nat → Option Nat) (f : α → Rd β)
    (items : List α) :
    (items.mapM f).run oracle = items.mapM (fun x => (f x).run oracle) := by
  unfold List.mapM
  let g := fun x => (f x).run oracle
  suffices h : ∀ (remaining : List α) (seen : List β),
      (List.mapM.loop f remaining seen).run oracle = List.mapM.loop g remaining seen by
    exact h items []
  intro remaining seen
  induction remaining generalizing seen with
  | nil => rfl
  | cons x xs ih =>
    change (Rd.bind (f x) (fun y => List.mapM.loop f xs (y :: seen))).run oracle =
      ((f x).run oracle).bind (fun y => List.mapM.loop g xs (y :: seen))
    rw [Rd.run_bind]
    simp only [ih]

private theorem mem_mapM {α β : Type} {g : α → Option β} {inputs : List α} {outputs : List β}
    {input : α} {output : β} (path : inputs.mapM g = some outputs)
    (member : input ∈ inputs) (computed : g input = some output) :
    output ∈ outputs := by
  induction inputs generalizing outputs with
  | nil => simp at member
  | cons next rest ih =>
    rw [List.mapM_cons] at path
    cases result : g next with
    | none => simp [result] at path
    | some value =>
      cases tail : rest.mapM g with
      | none => simp [result, tail] at path
      | some values =>
        simp [result, tail] at path
        subst outputs
        rcases List.mem_cons.mp member with equal | inRest
        · subst next
          rw [computed] at result
          exact List.mem_cons.mpr (.inl (Option.some.inj result))
        · exact List.mem_cons.mpr (.inr (ih tail inRest))

private theorem table_contains {dynamic : Elf.DynInfo} {regular : List Elf.Rela}
    (parsed : Dyn.frun Sqlite (Elf.relaTable dynamic Elf.DT_RELA
      ((dynamic.tag Elf.DT_RELASZ).getD 0 / 24)) = some regular)
    (witness : Dyn.frun Sqlite (Rd.bind (Rd.ofOption (dynamic.tagOff Elf.DT_RELA)) (fun base =>
      Rd.bind (Rd.guard (1170 < ((dynamic.tag Elf.DT_RELASZ).getD 0 / 24))) (fun _ =>
        Elf.rela (base + 24 * 1170)))) = some absoluteReloc) :
    absoluteReloc ∈ regular := by
  unfold Dyn.frun at parsed witness
  rw [Rd.run_bind] at witness
  obtain ⟨base, offset, checked⟩ := Option.bind_eq_some_iff.mp witness
  rw [Rd.run_bind] at checked
  obtain ⟨_, guard, read⟩ := Option.bind_eq_some_iff.mp checked
  have index : 1170 < (dynamic.tag Elf.DT_RELASZ).getD 0 / 24 := by
    unfold Rd.guard at guard
    split at guard
    · assumption
    · cases guard
  unfold Elf.relaTable at parsed
  rw [ite_eq_right (by omega)] at parsed
  change (Rd.bind (Rd.ofOption (dynamic.tagOff Elf.DT_RELA)) (fun base =>
    (List.range ((dynamic.tag Elf.DT_RELASZ).getD 0 / 24)).mapM
      (fun index => Elf.rela (base + 24 * index)))).run (blobRead Sqlite) = some regular at parsed
  rw [Rd.run_bind, offset, Option.bind_some, run_mapM] at parsed
  exact mem_mapM parsed (List.mem_range.mpr index) read

theorem absolute_relocation_mem {dynamic : Elf.DynInfo} {regular : List Elf.Rela}
    (headers : Dyn.finfo Sqlite = some dynamic)
    (parsed : Dyn.frun Sqlite (Elf.relaTable dynamic Elf.DT_RELA
      ((dynamic.tag Elf.DT_RELASZ).getD 0 / 24)) = some regular) :
    absoluteReloc ∈ regular := by
  have witness := absolute_relocation
  change (Rd.bind Elf.dynInfo (fun info =>
    Rd.bind (Rd.ofOption (info.tagOff Elf.DT_RELA)) (fun base =>
      Rd.bind (Rd.guard (1170 < ((info.tag Elf.DT_RELASZ).getD 0 / 24))) (fun _ =>
        Elf.rela (base + 24 * 1170))))).run (blobRead Sqlite) = some absoluteReloc at witness
  rw [Rd.run_bind, show Elf.dynInfo.run (blobRead Sqlite) = some dynamic from headers,
    Option.bind_some] at witness
  exact table_contains parsed witness

end Silmaril.Proofs.Elf.Corpus.SqliteMutex.Unlock.SlotTable
