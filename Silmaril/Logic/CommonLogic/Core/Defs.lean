module

public import Silmaril.Logic.Institution.Borrowing

@[expose] public section

namespace Silmaril.Logic.CommonLogic.Core

open CategoryTheory Silmaril.Logic.Institution

/-- Discourse names, non-discourse names, and free sequence markers are distinct classes. -/
structure Signature where
  discourse : Type
  nondiscourse : Type
  marker : Type

structure Signature.Hom (S T : Signature) where
  discourse : S.discourse → T.discourse
  nondiscourse : S.nondiscourse → T.nondiscourse
  marker : S.marker → T.marker

instance : Category Signature where
  Hom := Signature.Hom
  id _ := ⟨id, id, id⟩
  comp f g := ⟨g.discourse ∘ f.discourse, g.nondiscourse ∘ f.nondiscourse, g.marker ∘ f.marker⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- General reference/discourse semantics, following the open 2014 semantic account.
The discourse embeds into the reference universe; non-discourse names lie outside its image. -/
structure Model (S : Signature) where
  Reference : Type
  Discourse : Type
  nonempty : Nonempty Discourse
  embed : Discourse → Reference
  injective : Function.Injective embed
  discourse : S.discourse → Discourse
  nondiscourse : S.nondiscourse → Reference
  outside : ∀ n x, embed x ≠ nondiscourse n
  sequence : S.marker → List Discourse
  function : Reference → List Discourse → Discourse
  relation : Reference → List Discourse → Prop

/-- Homomorphisms preserve both universes, applications, sequence values, and relations. -/
structure Model.Hom {S : Signature} (M N : Model S) where
  reference : M.Reference → N.Reference
  discourse : M.Discourse → N.Discourse
  embed : ∀ x, reference (M.embed x) = N.embed (discourse x)
  name : ∀ n, discourse (M.discourse n) = N.discourse n
  nonname : ∀ n, reference (M.nondiscourse n) = N.nondiscourse n
  sequence : ∀ m, (M.sequence m).map discourse = N.sequence m
  function : ∀ r xs, discourse (M.function r xs) = N.function (reference r) (xs.map discourse)
  relation : ∀ r xs, M.relation r xs → N.relation (reference r) (xs.map discourse)

@[ext] theorem Model.Hom.ext {S : Signature} {M N : Model S} (f g : Model.Hom M N)
    (hr : f.reference = g.reference) (hd : f.discourse = g.discourse) : f = g := by
  cases f
  cases g
  cases hr
  cases hd
  rfl

instance {S : Signature} : Category (Model S) where
  Hom := Model.Hom
  id M := ⟨id, id, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => List.map_id _, fun _ _ => by simp only [id_eq, List.map_id],
    fun _ _ h => by simpa only [id_eq, List.map_id] using h⟩
  comp f g :=
    { reference := g.reference ∘ f.reference
      discourse := g.discourse ∘ f.discourse
      embed := fun x => by rw [Function.comp_apply, f.embed, g.embed]; rfl
      name := fun n => by rw [Function.comp_apply, f.name, g.name]
      nonname := fun n => by rw [Function.comp_apply, f.nonname, g.nonname]
      sequence := fun m => by rw [← List.map_map, f.sequence, g.sequence]
      function := fun r xs => by
        rw [Function.comp_apply, f.function, g.function, List.map_map]; rfl
      relation := fun r xs h => by
        have h' := g.relation _ _ (f.relation r xs h)
        simpa only [List.map_map, Function.comp_apply] using h' }
  id_comp f := Model.Hom.ext _ _ rfl rfl
  comp_id f := Model.Hom.ext _ _ rfl rfl
  assoc f g h := Model.Hom.ext _ _ rfl rfl

/-- Reduct changes symbol interpretations, retaining both universes and all extensions. -/
def Model.reduct {S T : Signature} (f : S ⟶ T) : Model T ⥤ Model S where
  obj M :=
    { Reference := M.Reference, Discourse := M.Discourse, nonempty := M.nonempty
      embed := M.embed, injective := M.injective
      discourse := M.discourse ∘ f.discourse
      nondiscourse := M.nondiscourse ∘ f.nondiscourse
      outside := fun n => M.outside (f.nondiscourse n)
      sequence := M.sequence ∘ f.marker
      function := M.function, relation := M.relation }
  map h :=
    { reference := h.reference, discourse := h.discourse, embed := h.embed
      name := fun n => h.name (f.discourse n)
      nonname := fun n => h.nonname (f.nondiscourse n)
      sequence := fun m => h.sequence (f.marker m)
      function := h.function, relation := h.relation }

/-- The three semantic kinds make the admitted well-formed core explicit. -/
inductive Kind where
  | individual | reference | sequence

/-- Well-formed terms and argument sequences. Individual-valued terms may be used as
reference heads through `lift`. A splice denotes an entire sequence, including the empty one. -/
inductive Expr (S : Signature) (n k : Nat) : Kind → Type where
  | var : Fin n → Expr S n k .individual
  | name : S.discourse → Expr S n k .individual
  | nonname : S.nondiscourse → Expr S n k .reference
  | lift : Expr S n k .individual → Expr S n k .reference
  | app : Expr S n k .reference → Expr S n k .sequence → Expr S n k .individual
  | nil : Expr S n k .sequence
  | cons : Expr S n k .individual → Expr S n k .sequence → Expr S n k .sequence
  | marker : S.marker → Expr S n k .sequence
  | seqvar : Fin k → Expr S n k .sequence
  | append : Expr S n k .sequence → Expr S n k .sequence → Expr S n k .sequence

abbrev Value {S : Signature} (M : Model S) : Kind → Type
  | .individual => M.Discourse
  | .reference => M.Reference
  | .sequence => List M.Discourse

namespace Expr

variable {S T U : Signature} {n k : Nat} {a : Kind}

def map (f : S ⟶ T) : {a : Kind} → Expr S n k a → Expr T n k a
  | _, .var i => .var i
  | _, .name d => .name (f.discourse d)
  | _, .nonname d => .nonname (f.nondiscourse d)
  | _, .lift t => .lift (t.map f)
  | _, .app t ts => .app (t.map f) (ts.map f)
  | _, .nil => .nil
  | _, .cons t ts => .cons (t.map f) (ts.map f)
  | _, .marker m => .marker (f.marker m)
  | _, .seqvar i => .seqvar i
  | _, .append xs ys => .append (xs.map f) (ys.map f)

@[simp] theorem map_id (t : Expr S n k a) : t.map (𝟙 S) = t := by
  induction t <;> simp_all [map] <;> rfl

@[simp] theorem map_comp (f : S ⟶ T) (g : T ⟶ U) (t : Expr S n k a) :
    t.map (f ≫ g) = (t.map f).map g := by
  induction t <;> simp_all [map] <;> rfl

def eval (M : Model S) (ρ : Fin n → M.Discourse) (σ : Fin k → List M.Discourse) :
    {a : Kind} → Expr S n k a → Value M a
  | _, .var i => ρ i
  | _, .name d => M.discourse d
  | _, .nonname d => M.nondiscourse d
  | _, .lift t => M.embed (t.eval M ρ σ)
  | _, .app t ts => M.function (t.eval M ρ σ) (ts.eval M ρ σ)
  | _, .nil => []
  | _, .cons t ts => t.eval M ρ σ :: ts.eval M ρ σ
  | _, .marker m => M.sequence m
  | _, .seqvar i => σ i
  | _, .append xs ys => xs.eval M ρ σ ++ ys.eval M ρ σ

@[simp] theorem eval_map (f : S ⟶ T) (M : Model T) (ρ : Fin n → M.Discourse)
    (σ : Fin k → List M.Discourse) (t : Expr S n k a) :
    (t.map f).eval M ρ σ = t.eval ((Model.reduct f).obj M) ρ σ := by
  induction t <;> simp_all [map, eval, Model.reduct]; rfl

end Expr

/-- Boolean formulas with independent individual and sequence scopes. -/
inductive Formula (S : Signature) : Nat → Nat → Type where
  | equal {n k} : Expr S n k .individual → Expr S n k .individual → Formula S n k
  | pred {n k} : Expr S n k .reference → Expr S n k .sequence → Formula S n k
  | tt {n k} : Formula S n k
  | ff {n k} : Formula S n k
  | neg {n k} : Formula S n k → Formula S n k
  | conj {n k} : Formula S n k → Formula S n k → Formula S n k
  | disj {n k} : Formula S n k → Formula S n k → Formula S n k
  | impl {n k} : Formula S n k → Formula S n k → Formula S n k
  | iff {n k} : Formula S n k → Formula S n k → Formula S n k
  | all {n k} : Formula S (n+1) k → Formula S n k
  | ex {n k} : Formula S (n+1) k → Formula S n k
  | allSeq {n k} : Formula S n (k+1) → Formula S n k
  | exSeq {n k} : Formula S n (k+1) → Formula S n k

namespace Formula

variable {S T U : Signature} {n k : Nat}

def map (f : S ⟶ T) : {n k : Nat} → Formula S n k → Formula T n k
  | _, _, .equal t u => .equal (t.map f) (u.map f)
  | _, _, .pred t ts => .pred (t.map f) (ts.map f)
  | _, _, .tt => .tt
  | _, _, .ff => .ff
  | _, _, .neg p => .neg (p.map f)
  | _, _, .conj p q => .conj (p.map f) (q.map f)
  | _, _, .disj p q => .disj (p.map f) (q.map f)
  | _, _, .impl p q => .impl (p.map f) (q.map f)
  | _, _, .iff p q => .iff (p.map f) (q.map f)
  | _, _, .all p => .all (p.map f)
  | _, _, .ex p => .ex (p.map f)
  | _, _, .allSeq p => .allSeq (p.map f)
  | _, _, .exSeq p => .exSeq (p.map f)

@[simp] theorem map_id (p : Formula S n k) : p.map (𝟙 S) = p := by
  induction p <;> simp_all [map]

@[simp] theorem map_comp (f : S ⟶ T) (g : T ⟶ U) (p : Formula S n k) :
    p.map (f ≫ g) = (p.map f).map g := by
  induction p <;> simp_all [map]

def Holds (M : Model S) : {n k : Nat} → (Fin n → M.Discourse) →
    (Fin k → List M.Discourse) → Formula S n k → Prop
  | _, _, ρ, σ, .equal t u => t.eval M ρ σ = u.eval M ρ σ
  | _, _, ρ, σ, .pred t ts => M.relation (t.eval M ρ σ) (ts.eval M ρ σ)
  | _, _, _, _, .tt => True
  | _, _, _, _, .ff => False
  | _, _, ρ, σ, .neg p => ¬ p.Holds M ρ σ
  | _, _, ρ, σ, .conj p q => p.Holds M ρ σ ∧ q.Holds M ρ σ
  | _, _, ρ, σ, .disj p q => p.Holds M ρ σ ∨ q.Holds M ρ σ
  | _, _, ρ, σ, .impl p q => p.Holds M ρ σ → q.Holds M ρ σ
  | _, _, ρ, σ, .iff p q => p.Holds M ρ σ ↔ q.Holds M ρ σ
  | _, _, ρ, σ, .all p => ∀ x, p.Holds M (Fin.cases x ρ) σ
  | _, _, ρ, σ, .ex p => ∃ x, p.Holds M (Fin.cases x ρ) σ
  | _, _, ρ, σ, .allSeq p => ∀ xs : List M.Discourse, p.Holds M ρ (Fin.cases xs σ)
  | _, _, ρ, σ, .exSeq p => ∃ xs : List M.Discourse, p.Holds M ρ (Fin.cases xs σ)

@[simp] theorem holds_map (f : S ⟶ T) (M : Model T) (ρ : Fin n → M.Discourse)
    (σ : Fin k → List M.Discourse) (p : Formula S n k) :
    (p.map f).Holds M ρ σ ↔ p.Holds ((Model.reduct f).obj M) ρ σ := by
  induction p <;> simp_all [map, Holds] <;> rfl

end Formula

abbrev Sentence (S : Signature) := Formula S 0 0

def room (S : Signature) : Room.{0,0,1} :=
  ⟨Sentence S, Cat.of (Model S), fun M p => p.Holds M Fin.elim0 Fin.elim0⟩

def corridor {S T : Signature} (f : S ⟶ T) : room S ⟶ room T :=
  ⟨Formula.map f, Model.reduct f, fun M p => Formula.holds_map f M _ _ p⟩

def institution : Signature ⥤ Room.{0,0,1} where
  obj := room
  map := corridor
  map_id _S := Room.hom_ext (funext Formula.map_id) rfl
  map_comp f g := Room.hom_ext (funext (Formula.map_comp f g)) rfl

def inst : Inst.{1,0,0,0,1} := ⟨Signature, institution⟩

end Silmaril.Logic.CommonLogic.Core
