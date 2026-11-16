module

public import Silmaril.Logic.CommonLogic.Core.FirstOrder.Defs
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

@[expose] public section

namespace Silmaril.Logic.CommonLogic.FirstOrder

open Silmaril.Logic.CommonLogic
open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples

/-- Independent single-sorted operation and predicate symbols, including arity zero. -/
structure Signature where
  Op : Nat → Type
  Rel : Nat → Type

structure Signature.Hom (S T : Signature) where
  ops : ∀ n, S.Op n → T.Op n
  rels : ∀ n, S.Rel n → T.Rel n

instance : Category Signature where
  Hom := Signature.Hom
  id _ := ⟨fun _ => id, fun _ => id⟩
  comp f g := ⟨fun n => g.ops n ∘ f.ops n, fun n => g.rels n ∘ f.rels n⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Actual public FOL signatures, with one sort and no restriction on symbol arities. -/
abbrev publicSignature (S : Signature) : FOL.Signature :=
  ⟨⟨Unit, fun n _ _ => S.Op n⟩, fun n _ => S.Rel n⟩

def publicMap {S T : Signature} (f : S ⟶ T) : publicSignature S ⟶ publicSignature T :=
  { sorts := id, ops := fun {n} => f.ops n, rels := fun {n} => f.rels n }

abbrev publicSignatures : Signature ⥤ FOL.Signature where
  obj := publicSignature
  map := publicMap
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Public FOL restricted only in signature sorts, retaining all its structures and arrows. -/
def institution : Signature ⥤ Room.{0,0,1} := publicSignatures ⋙ FOL.institution

def inst : Inst.{1,0,0,0,1} := ⟨Signature, institution⟩

/-- Tagged names keep every operation and predicate head independent, even at different arities. -/
abbrev Heads (S : Signature) := (Σ n, S.Op n) ⊕ (Σ n, S.Rel n)

/-- A discourse object is an individual; a reference may also lie outside the discourse.
All translated symbol names are non-discourse references. No sequence markers are used. -/
abbrev clSignature (S : Signature) : Core.Signature := ⟨Empty, Heads S, Empty⟩

def clMap {S T : Signature} (f : S ⟶ T) : clSignature S ⟶ clSignature T :=
  ⟨Empty.elim, fun h => match h with
    | .inl ⟨n,o⟩ => .inl ⟨n,f.ops n o⟩
    | .inr ⟨n,r⟩ => .inr ⟨n,f.rels n r⟩, Empty.elim⟩

private theorem clHom_ext {S T : Core.Signature}
    (f g : S ⟶ T) (hd : f.discourse = g.discourse)
    (hn : f.nondiscourse = g.nondiscourse) (hm : f.marker = g.marker) : f = g := by
  cases f; cases g; cases hd; cases hn; cases hm; rfl

@[simp] theorem clMap_id (S : Signature) : clMap (𝟙 S) = 𝟙 (clSignature S) := by
  apply clHom_ext
  · funext x; exact Empty.elim x
  · funext h; cases h with
    | inl h => cases h; rfl
    | inr h => cases h; rfl
  · funext x; exact Empty.elim x

@[simp] theorem clMap_comp {S T U : Signature} (f : S ⟶ T) (g : T ⟶ U) :
    clMap (f ≫ g) = clMap f ≫ clMap g := by
  apply clHom_ext
  · funext x; exact Empty.elim x
  · funext h; cases h with
    | inl h => cases h; rfl
    | inr h => cases h; rfl
  · funext x; exact Empty.elim x

def signatures : Signature ⥤ Core.Signature where
  obj := clSignature
  map := clMap
  map_id := clMap_id
  map_comp := clMap_comp

/-- Decode an arbitrary CL model, ignoring applications outside each symbol's declared arity. -/
abbrev decode {S : Signature} (M : Core.Model (clSignature S)) : FOL.Structure (publicSignature S) where
  carrier _ := M.Discourse
  op := fun {n} _ _ o args => M.function (M.nondiscourse (.inl ⟨n,o⟩)) (List.ofFn args)
  rel := fun {n} _ r args => M.relation (M.nondiscourse (.inr ⟨n,r⟩)) (List.ofFn args)

/-- Every actual CL homomorphism gives a public FOL homomorphism, without injectivity restrictions. -/
def decodeHom {S : Signature} {M N : Core.Model (clSignature S)} (h : M ⟶ N) :
    decode M ⟶ decode N where
  map _ := h.discourse
  map_op o args := by
    dsimp [decode]
    simpa only [h.nonname, List.map_ofFn, Function.comp_def] using h.function (M.nondiscourse (.inl ⟨_,o⟩)) (List.ofFn args)
  map_rel r args hr := by
    have hh := h.relation _ _ hr
    simpa only [decode, h.nonname, List.map_ofFn, Function.comp_def] using hh

def models (S : Signature) : Core.Model (clSignature S) ⥤ FOL.Structure (publicSignature S) where
  obj := decode
  map := decodeHom
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev tuple := @Core.FirstOrder.tuple

/-- Compile only fixed named heads and finite tuples; CL computed heads and sequence binders
are outside the source fragment. -/
def term {S : Signature} {n k : Nat} {Γ : Fin n → Unit} :
    {s : Unit} → EQ.Term (publicSignature S).toSignature Γ s → Core.Expr (clSignature S) n k .individual
  | _, .var i => .var i
  | _, .app (n := m) o args =>
      .app (.nonname (.inl ⟨m,o⟩)) (tuple (fun i => term (args i)))

def formula {S : Signature} : {n k : Nat} → {Γ : Fin n → Unit} →
    FOL.Formula (publicSignature S) Γ → Core.Formula (clSignature S) n k
  | _, _, _, .eq t u => .equal (term t) (term u)
  | _, _, _, .rel (n := m) r args =>
      .pred (.nonname (.inr ⟨m,r⟩)) (tuple (fun i => term (args i)))
  | _, _, _, .tt => .tt
  | _, _, _, .not p => .neg (formula p)
  | _, _, _, .and p q => .conj (formula p) (formula q)
  | _, _, _, .all _ p => .all (formula p)

def sentence {S : Signature} (p : FOL.Sentence (publicSignature S)) : Core.Sentence (clSignature S) :=
  formula p.formula

/-- Nonempty structures form a full subcategory: no public FOL arrows are discarded. -/
def inhabited (S : Signature) : ObjectProperty (FOL.Structure (publicSignature S)) :=
  fun M => Nonempty (M.carrier ())

abbrev NonemptyModel (S : Signature) := (inhabited S).FullSubcategory

def nonemptyReduct {S T : Signature} (f : S ⟶ T) : NonemptyModel T ⥤ NonemptyModel S :=
  (inhabited S).lift ((inhabited T).ι ⋙ FOL.Structure.reduct (publicMap f))
    (fun M => M.property)

def nonemptyRoom (S : Signature) : Room.{0,0,1} :=
  ⟨FOL.Sentence (publicSignature S), Cat.of (NonemptyModel S), fun M p => p.Holds M.obj⟩

def nonemptyCorridor {S T : Signature} (f : S ⟶ T) : nonemptyRoom S ⟶ nonemptyRoom T :=
  ⟨FOL.Sentence.map (publicMap f), nonemptyReduct f,
    fun M p => FOL.Sentence.holds_map (publicMap f) M.obj p⟩

def nonemptyInstitution : Signature ⥤ Room.{0,0,1} where
  obj := nonemptyRoom
  map := nonemptyCorridor
  map_id _S := Room.hom_ext (funext (FOL.Sentence.map_id)) rfl
  map_comp f g := Room.hom_ext (funext (FOL.Sentence.map_comp (publicMap f) (publicMap g))) rfl

def nonemptyInst : Inst.{1,0,0,0,1} := ⟨Signature, nonemptyInstitution⟩

def nonemptyModels (S : Signature) : Core.Model (clSignature S) ⥤ NonemptyModel S :=
  (inhabited S).lift (models S) (fun M => M.nonempty)

end Silmaril.Logic.CommonLogic.FirstOrder
