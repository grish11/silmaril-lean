module

public import Silmaril.Logic.CommonLogic.Source.CLIF.Defs

@[expose] public section
namespace Silmaril.Logic.CommonLogic.Source.CLIF
open CategoryTheory Silmaril.Logic.Institution

/-- Read success is a checked equation, not a claim that every CLIF dialect is accepted. -/
def readText? {S : Core.Signature} (names : Names S) (valid : names.Valid)
    (fuel : Nat) (source : String) : Option (Text names) :=
  match hp : read fuel source with
  | none => none
  | some raw => match ht : raw.mapM (Source.Formula.elaborate names [] []) with
    | none => none
    | some typed => some ⟨valid, source, fuel, raw, typed, hp, ht⟩

theorem list_adequacy {S : Core.Signature} (names : Names S) (M : Core.Model S)
    (raw : List Source.Formula) : ∀ typed,
    raw.mapM (Source.Formula.elaborate names [] []) = some typed →
    ((∀ p ∈ raw, p.Holds names M (fun _ => none) (fun _ => none)) ↔
      ∀ p ∈ typed, p.Holds M Fin.elim0 Fin.elim0) := by
  induction raw with
  | nil =>
      intro typed h
      simp at h
      subst typed
      simp
  | cons p rest ih =>
      intro typed h
      cases hp : p.elaborate names [] [] <;>
        cases hr : rest.mapM (Source.Formula.elaborate names [] []) <;>
        simp [hp, hr] at h
      subst typed
      rw [List.forall_mem_cons, List.forall_mem_cons]
      exact and_congr
        (p.holds_of_elaborated names M [] [] _ hp Fin.elim0 Fin.elim0) (ih _ hr)

def conjunction {S : Core.Signature} (ps : List (Core.Sentence S)) : Core.Sentence S :=
  ps.foldr Core.Formula.conj .tt

theorem conjunction_holds {S : Core.Signature} (M : Core.Model S) (ps : List (Core.Sentence S)) :
    (conjunction ps).Holds M Fin.elim0 Fin.elim0 ↔ ∀ p ∈ ps, p.Holds M Fin.elim0 Fin.elim0 := by
  induction ps with
  | nil => simp [conjunction, Core.Formula.Holds]
  | cons p ps ih => simpa only [conjunction, List.foldr_cons, Core.Formula.Holds,
      List.forall_mem_cons] using and_congr Iff.rfl ih

/-- Complete source text satisfaction uses every parsed sentence in one model. -/
def room {S : Core.Signature} (names : Names S) : Room.{0,0,1} :=
  ⟨Text names, Cat.of (Core.Model S), fun M text =>
    ∀ p ∈ text.raw, p.Holds names M (fun _ => none) (fun _ => none)⟩

def toCore {S : Core.Signature} (names : Names S) : room names ⟶ Core.room S where
  sen text := conjunction text.typed
  mod := 𝟭 _
  sat M text := (conjunction_holds M text.typed).trans
    (list_adequacy names M text.raw text.typed text.elaborated).symm

theorem toCore_modelExpansive {S : Core.Signature} (names : Names S) :
    (toCore names).ModelExpansive := fun M => ⟨M,rfl⟩

theorem consequence_iff {S : Core.Signature} (names : Names S)
    (Γ : Set (Text names)) (text : Text names) :
    (Core.room S).Entails ((toCore names).sen '' Γ) ((toCore names).sen text) ↔
      (room names).Entails Γ text :=
  ((toCore names).entails_map_iff (toCore_modelExpansive names) Γ text).symm

/-- Raw source strings and binder spellings are unchanged under semantic symbol maps. -/
theorem elaborate_list_map {S T : Core.Signature} (names : Names S) (f : S ⟶ T)
    (raw : List Source.Formula) :
    raw.mapM (Source.Formula.elaborate (names.map f) [] []) =
      (raw.mapM (Source.Formula.elaborate names [] [])).map (List.map (Core.Formula.map f)) := by
  induction raw with
  | nil => rfl
  | cons p rest ih =>
      simp only [List.mapM_cons, Source.Formula.elaborate_map, ih]
      cases p.elaborate names [] [] <;>
        cases rest.mapM (Source.Formula.elaborate names [] []) <;> rfl

def Text.map {S T : Core.Signature} {names : Names S} (f : S ⟶ T)
    (text : Text names) : Text (names.map f) where
  declarations_valid := names.valid_map f text.declarations_valid
  source := text.source
  fuel := text.fuel
  raw := text.raw
  typed := text.typed.map (Core.Formula.map f)
  parsed := text.parsed
  elaborated := by rw [elaborate_list_map, text.elaborated]; rfl

def corridor {S T : Core.Signature} (names : Names S) (f : S ⟶ T) :
    room names ⟶ room (names.map f) where
  sen := Text.map f
  mod := Core.Model.reduct f
  sat M text := by
    rw [show (room (names.map f)).Sat M (text.map f) ↔
      ∀ p ∈ (text.map f).typed, p.Holds M Fin.elim0 Fin.elim0 from
      list_adequacy (names.map f) M _ _ (text.map f).elaborated]
    rw [show (room names).Sat ((Core.Model.reduct f).obj M) text ↔
      ∀ p ∈ text.typed, p.Holds ((Core.Model.reduct f).obj M) Fin.elim0 Fin.elim0 from
      list_adequacy names _ _ _ text.elaborated]
    simp only [Text.map, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      ]
    exact forall_congr' fun p => forall_congr' fun _ =>
      Core.Formula.holds_map f M Fin.elim0 Fin.elim0 p

end Silmaril.Logic.CommonLogic.Source.CLIF
