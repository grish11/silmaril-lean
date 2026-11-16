module

public import Silmaril.Logic.CommonLogic.Core.Thms

@[expose] public section
namespace Silmaril.Logic.CommonLogic.Source
open CategoryTheory Silmaril.Logic.Institution

/-- An explicit source vocabulary. Spellings are local to this environment;
semantic symbols can have arbitrary types, with aliases permitted. -/
structure Names (S : Core.Signature) where
  discourse : List (String × S.discourse)
  nondiscourse : List (String × S.nondiscourse)
  marker : List (String × S.marker)

def find? {α : Type} (name : String) : List (String × α) → Option α
  | [] => none
  | (key,value)::rest => if name == key then some value else find? name rest

/-- Change semantic symbols through any class-preserving Core signature map.
Source spellings and lexical binders stay fixed, so this cannot capture variables. -/
def Names.map {S T : Core.Signature} (names : Names S) (f : S ⟶ T) : Names T where
  discourse := names.discourse.map (fun p => (p.1, f.discourse p.2))
  nondiscourse := names.nondiscourse.map (fun p => (p.1, f.nondiscourse p.2))
  marker := names.marker.map (fun p => (p.1, f.marker p.2))

/-- Source declarations are an explicit partition, with unique spellings in
 each class. Multiple spellings may still denote the same semantic symbol. -/
def Names.Valid {S : Core.Signature} (names : Names S) : Prop :=
  (names.discourse.map Prod.fst).Nodup ∧
  (names.nondiscourse.map Prod.fst).Nodup ∧
  (names.marker.map Prod.fst).Nodup ∧
  (∀ d ∈ names.discourse.map Prod.fst, d ∉ names.nondiscourse.map Prod.fst) ∧
  (∀ m ∈ names.marker.map Prod.fst, m ∉ names.discourse.map Prod.fst) ∧
  (∀ m ∈ names.marker.map Prod.fst, m ∉ names.nondiscourse.map Prod.fst)

/-- First-match lexical lookup, independently in the two binder classes. -/
def index? (name : String) : (names : List String) → Option (Fin names.length)
  | [] => none
  | key::rest => if name == key then some 0 else (index? name rest).map Fin.succ

def assignment {α : Type} (names : List String) (values : Fin names.length → α)
    (name : String) : Option α := (index? name names).map values

/-- Raw, named surface expressions. Names have no attached semantic symbol or
scope proof. The kinds express the admitted segregated Core grammar. -/
inductive Expr : Core.Kind → Type where
  | individual : String → Expr .individual
  | reference : String → Expr .reference
  | sequence : String → Expr .sequence
  | lift : Expr .individual → Expr .reference
  | app : Expr .reference → Expr .sequence → Expr .individual
  | nil : Expr .sequence
  | cons : Expr .individual → Expr .sequence → Expr .sequence
  | append : Expr .sequence → Expr .sequence → Expr .sequence

inductive Formula where
  | equal : Expr .individual → Expr .individual → Formula
  | pred : Expr .reference → Expr .sequence → Formula
  | tt | ff
  | neg : Formula → Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  | impl : Formula → Formula → Formula
  | iff : Formula → Formula → Formula
  | all : String → Formula → Formula
  | ex : String → Formula → Formula
  | allSeq : String → Formula → Formula
  | exSeq : String → Formula → Formula

/-- Raw interpretation resolves spellings directly. No elaborator, typed term,
or adequacy hypothesis occurs in this definition. -/
def Expr.eval {S : Core.Signature} (names : Names S) (M : Core.Model S)
    (ρ : String → Option M.Discourse) (σ : String → Option (List M.Discourse)) :
    {a : Core.Kind} → Expr a → Option (Core.Value M a)
  | _, .individual name => ρ name <|> (find? name names.discourse).map M.discourse
  | _, .reference name =>
      ((ρ name <|> (find? name names.discourse).map M.discourse).map M.embed) <|>
        (find? name names.nondiscourse).map M.nondiscourse
  | _, .sequence name => σ name <|> (find? name names.marker).map M.sequence
  | _, .lift t => (t.eval names M ρ σ).map M.embed
  | _, .app h args => do pure (M.function (← h.eval names M ρ σ) (← args.eval names M ρ σ))
  | _, .nil => some []
  | _, .cons t ts => do pure ((← t.eval names M ρ σ) :: (← ts.eval names M ρ σ))
  | _, .append xs ys => do pure ((← xs.eval names M ρ σ) ++ (← ys.eval names M ρ σ))

def bind {α : Type} (ρ : String → Option α) (name : String) (value : α) : String → Option α :=
  fun key => if key == name then some value else ρ key

def Formula.Holds {S : Core.Signature} (names : Names S) (M : Core.Model S)
    (ρ : String → Option M.Discourse) (σ : String → Option (List M.Discourse)) : Formula → Prop
  | .equal t u => ∃ x y, t.eval names M ρ σ = some x ∧ u.eval names M ρ σ = some y ∧ x = y
  | .pred h args => ∃ r xs, h.eval names M ρ σ = some r ∧ args.eval names M ρ σ = some xs ∧ M.relation r xs
  | .tt => True
  | .ff => False
  | .neg p => ¬ p.Holds names M ρ σ
  | .conj p q => p.Holds names M ρ σ ∧ q.Holds names M ρ σ
  | .disj p q => p.Holds names M ρ σ ∨ q.Holds names M ρ σ
  | .impl p q => p.Holds names M ρ σ → q.Holds names M ρ σ
  | .iff p q => p.Holds names M ρ σ ↔ q.Holds names M ρ σ
  | .all name p => ∀ x, p.Holds names M (bind ρ name x) σ
  | .ex name p => ∃ x, p.Holds names M (bind ρ name x) σ
  | .allSeq name p => ∀ xs : List M.Discourse, p.Holds names M ρ (bind σ name xs)
  | .exSeq name p => ∃ xs : List M.Discourse, p.Holds names M ρ (bind σ name xs)

/-- Elaboration is structural, not a semantic certificate supplied by a caller. -/
def Expr.elaborate {S : Core.Signature} (names : Names S) (ι κ : List String) :
    {a : Core.Kind} → Expr a → Option (Core.Expr S ι.length κ.length a)
  | _, .individual name =>
      match index? name ι with
      | some i => some (.var i)
      | none => (find? name names.discourse).map Core.Expr.name
  | _, .reference name =>
      match index? name ι with
      | some i => some (.lift (.var i))
      | none => match find? name names.discourse with
        | some d => some (.lift (.name d))
        | none => (find? name names.nondiscourse).map Core.Expr.nonname
  | _, .sequence name =>
      match index? name κ with
      | some i => some (.seqvar i)
      | none => (find? name names.marker).map Core.Expr.marker
  | _, .lift t => (t.elaborate names ι κ).map Core.Expr.lift
  | _, .app h args => do pure (.app (← h.elaborate names ι κ) (← args.elaborate names ι κ))
  | _, .nil => some .nil
  | _, .cons t ts => do pure (.cons (← t.elaborate names ι κ) (← ts.elaborate names ι κ))
  | _, .append xs ys => do pure (.append (← xs.elaborate names ι κ) (← ys.elaborate names ι κ))

def Formula.elaborate {S : Core.Signature} (names : Names S) :
    (ι κ : List String) → Formula → Option (Core.Formula S ι.length κ.length)
  | ι, κ, .equal t u => do pure (.equal (← t.elaborate names ι κ) (← u.elaborate names ι κ))
  | ι, κ, .pred h args => do pure (.pred (← h.elaborate names ι κ) (← args.elaborate names ι κ))
  | _, _, .tt => some .tt
  | _, _, .ff => some .ff
  | ι, κ, .neg p => (p.elaborate names ι κ).map Core.Formula.neg
  | ι, κ, .conj p q => do pure (.conj (← p.elaborate names ι κ) (← q.elaborate names ι κ))
  | ι, κ, .disj p q => do pure (.disj (← p.elaborate names ι κ) (← q.elaborate names ι κ))
  | ι, κ, .impl p q => do pure (.impl (← p.elaborate names ι κ) (← q.elaborate names ι κ))
  | ι, κ, .iff p q => do pure (.iff (← p.elaborate names ι κ) (← q.elaborate names ι κ))
  | ι, κ, .all name p => (p.elaborate names (name::ι) κ).map Core.Formula.all
  | ι, κ, .ex name p => (p.elaborate names (name::ι) κ).map Core.Formula.ex
  | ι, κ, .allSeq name p => (p.elaborate names ι (name::κ)).map Core.Formula.allSeq
  | ι, κ, .exSeq name p => (p.elaborate names ι (name::κ)).map Core.Formula.exSeq

/-- An accepted closed source formula retains its syntax and computed elaboration. -/
structure Sentence {S : Core.Signature} (names : Names S) where
  declarations_valid : names.Valid
  raw : Formula
  typed : Core.Sentence S
  decoded : raw.elaborate names [] [] = some typed

def room {S : Core.Signature} (names : Names S) : Room.{0,0,1} :=
  ⟨Sentence names, Cat.of (Core.Model S), fun M p => p.raw.Holds names M (fun _ => none) (fun _ => none)⟩

end Silmaril.Logic.CommonLogic.Source
