module

public import Silmaril.Logic.CommonLogic.Source.Presentations.Thms
public import Silmaril.Logic.CommonLogic.Source.Vocabulary.Thms

/-! Named source vocabularies vary through actual Core symbol functions.
Arrows preserve successful class-sensitive spelling lookup and allow fresh
target declarations. Raw spelling renaming is separate.
Each room retains the full Core model category and every accepted text. -/
@[expose] public section
namespace Silmaril.Logic.CommonLogic.Source.Presentations.Family
open CategoryTheory Silmaril.Logic.Institution

structure Signature where
  core : Core.Signature
  names : Names core
  valid : names.Valid

@[simp] theorem names_map_id {S : Core.Signature} (names : Names S) :
    names.map (𝟙 S) = names := by
  cases names
  change Names.mk (List.map id _) (List.map id _) (List.map id _) = _
  simp only [List.map_id]

theorem names_map_comp {S T U : Core.Signature} (names : Names S)
    (f : S ⟶ T) (g : T ⟶ U) : (names.map f).map g = names.map (f ≫ g) := by
  cases names
  simp only [Names.map, List.map_map]
  rfl

/-- The symbol functions may identify symbols. Table compatibility fixes their
spellings, not the signature or semantic interpretation. Aliases remain allowed. -/
structure Signature.Hom (A B : Signature) where
  symbols : A.core ⟶ B.core
  named : A.names.Supports B.names symbols

@[ext] theorem Signature.Hom.ext {A B : Signature} (f g : Signature.Hom A B)
    (same : f.symbols = g.symbols) : f = g := by
  cases f
  cases g
  cases same
  rfl

instance : Category Signature where
  Hom := Signature.Hom
  id _ := ⟨𝟙 _, Names.Supports.refl _⟩
  comp f g := ⟨f.symbols ≫ g.symbols, f.named.trans g.named⟩
  id_comp _ := Signature.Hom.ext _ _ rfl
  comp_id _ := Signature.Hom.ext _ _ rfl
  assoc _ _ _ := Signature.Hom.ext _ _ rfl

def forget : Signature ⥤ Core.Signature where
  obj A := A.core
  map f := f.symbols
  map_id _ := rfl
  map_comp _ _ := rfl

theorem elaborate_list_supports {S T : Core.Signature} {a : Names S} {b : Names T}
    {f : S ⟶ T} (h : a.Supports b f) (raw : List Formula) (typed : List (Core.Sentence S))
    (decoded : raw.mapM (Formula.elaborate a [] []) = some typed) :
    raw.mapM (Formula.elaborate b [] []) = some (typed.map (Core.Formula.map f)) := by
  induction raw generalizing typed with
  | nil =>
      have same : [] = typed := Option.some.inj decoded
      subst typed
      rfl
  | cons p ps ih =>
      cases hp : p.elaborate a [] [] <;>
        cases hs : ps.mapM (Formula.elaborate a [] []) <;>
        simp [List.mapM_cons, hp, hs] at decoded
      subst typed
      simp [List.mapM_cons, p.elaborate_supports h [] [] _ hp, ih _ hs]

/-- The old table-equality case is a useful constructor, not a restriction on arrows. -/
def Signature.Hom.ofNamed {A B : Signature} (f : A.core ⟶ B.core)
    (named : B.names = A.names.map f) : A ⟶ B :=
  ⟨f, named ▸ Names.supports_map A.names f⟩

/-- Reuse the exact original byte string and parser equation. Only semantic
symbols in the computed typed elaboration change. -/
def mapText {A B : Signature} (f : A ⟶ B) (text : CLIF.Text A.names) : CLIF.Text B.names where
  declarations_valid := B.valid
  source := text.source
  fuel := text.fuel
  raw := text.raw
  typed := text.typed.map (Core.Formula.map f.symbols)
  parsed := text.parsed
  elaborated := elaborate_list_supports f.named text.raw text.typed text.elaborated

@[ext] theorem text_ext {S : Core.Signature} {names : Names S} (p q : CLIF.Text names)
    (source : p.source = q.source) (fuel : p.fuel = q.fuel)
    (raw : p.raw = q.raw) (typed : p.typed = q.typed) : p = q := by
  cases p
  cases q
  cases source
  cases fuel
  cases raw
  cases typed
  rfl

@[simp] theorem mapText_id (A : Signature) (text : CLIF.Text A.names) :
    mapText (𝟙 A) text = text := by
  apply text_ext <;> try rfl
  change text.typed.map (Core.Formula.map (𝟙 A.core)) = text.typed
  have identity (ps : List (Core.Sentence A.core)) :
      ps.map (Core.Formula.map (𝟙 A.core)) = ps := by
    induction ps with
    | nil => rfl
    | cons p ps ih => simp only [List.map_cons, Core.Formula.map_id, ih]
  exact identity text.typed

theorem mapText_comp {A B C : Signature} (f : A ⟶ B) (g : B ⟶ C)
    (text : CLIF.Text A.names) : mapText (f ≫ g) text = mapText g (mapText f text) := by
  apply text_ext <;> try rfl
  simp only [mapText, List.map_map]
  congr 1
  funext p
  exact Core.Formula.map_comp f.symbols g.symbols p

/-- Every actual Core homomorphism remains a model arrow. -/
def corridor {A B : Signature} (f : A ⟶ B) : CLIF.room A.names ⟶ CLIF.room B.names where
  sen := mapText f
  mod := Core.Model.reduct f.symbols
  sat M text := by
    rw [show (CLIF.room B.names).Sat M (mapText f text) ↔
      ∀ p ∈ (mapText f text).typed, p.Holds M Fin.elim0 Fin.elim0 from
      CLIF.list_adequacy B.names M _ _ (mapText f text).elaborated]
    rw [show (CLIF.room A.names).Sat ((Core.Model.reduct f.symbols).obj M) text ↔
      ∀ p ∈ text.typed, p.Holds ((Core.Model.reduct f.symbols).obj M) Fin.elim0 Fin.elim0 from
      CLIF.list_adequacy A.names _ _ _ text.elaborated]
    simp only [mapText, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact forall_congr' fun p => forall_congr' fun _ =>
      Core.Formula.holds_map f.symbols M Fin.elim0 Fin.elim0 p

def institution : Signature ⥤ Room.{0,0,1} where
  obj A := CLIF.room A.names
  map := corridor
  map_id A := Room.hom_ext (funext (mapText_id A)) rfl
  map_comp f g := Room.hom_ext (funext (mapText_comp f g)) rfl

def inst : Inst.{1,0,0,0,1} := ⟨Signature, institution⟩

theorem conjunction_map {S T : Core.Signature} (f : S ⟶ T) (ps : List (Core.Sentence S)) :
    (CLIF.conjunction ps).map f = CLIF.conjunction (ps.map (Core.Formula.map f)) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simpa only [CLIF.conjunction, List.foldr_cons,
      Core.Formula.map, List.map_cons] using congrArg (Core.Formula.conj (p.map f)) ih

/-- A genuine varying-signature source-to-Core comorphism. -/
def toCore : Inst.CoHom inst Core.inst where
  Φ := forget
  ρ :=
    { app A := CLIF.toCore A.names
      naturality := fun {_ _} f =>
        Room.hom_ext (funext fun text => (conjunction_map f.symbols text.typed).symm) rfl }

/-- Composition uses the existing full-Core/public-FOL comparison without
restricting its sentence language or its actual constrained model category. -/
noncomputable def toFOL : Inst.CoHom inst FiniteListFOL.inst :=
  Inst.CoHom.comp toCore FiniteListFOL.comorphism

end Silmaril.Logic.CommonLogic.Source.Presentations.Family
