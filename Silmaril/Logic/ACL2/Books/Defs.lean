module

public import Silmaril.Logic.ACL2.Thms

@[expose] public section

namespace Silmaril.Logic.ACL2

open CategoryTheory

namespace Signature

def add (S : Signature) (name : Name) (n : Nat) : Signature :=
  ⟨fun f => if f = name then some n else S.arity f⟩

def addSymbol (S : Signature) (name : Name) (n : Nat) : (S.add name n).Symbol n :=
  ⟨name, by simp [add]⟩

theorem ne_of_fresh {S : Signature} {name : Name} {n : Nat} (fresh : S.arity name = none)
    (f : S.Symbol n) : f.val ≠ name := by
  intro h
  have hf := f.property
  simp [h, fresh] at hf

def addInclusion {S : Signature} {name : Name} (fresh : S.arity name = none) (n : Nat) :
    S ⟶ S.add name n where
  preserve := by
    intro f k declared
    simpa [add, ne_of_fresh fresh ⟨f, declared⟩] using declared

end Signature

/-- A named function's defining equation, with one distinct formal variable per argument. -/
def definitionEquation {S : Signature} {n : Nat} (f : S.Symbol n) (body : Term S n) : Sentence S :=
  .eq (.app f .var) body

/-- A π-signature contains declarations and retains the actual named definition bodies.
A presentation can be assembled directly. Sequential admission is tracked separately by `Book`. -/
structure Presentation where
  signature : Signature
  body : ∀ {n}, signature.Symbol n → Option (Term signature n)

namespace Presentation

def bare (S : Signature) : Presentation := ⟨S, fun _ => none⟩

def equations (P : Presentation) : Set (Sentence P.signature) :=
  {p | ∃ (n : Nat) (f : P.signature.Symbol n) (t : Term P.signature n),
    P.body f = some t ∧ p = definitionEquation f t}

def Models (P : Presentation) (M : Model P.signature) : Prop :=
  ∀ p ∈ P.equations, p.Holds M

def Derives (P : Presentation) (Γ : Set (Sentence P.signature)) (p : Sentence P.signature) : Prop :=
  ACL2.Derives (P.equations ∪ Γ) p

/-- Structure-preserving arrows retain each defined name and translate its body. -/
structure Hom (P Q : Presentation) where
  signature : P.signature ⟶ Q.signature
  body : ∀ {n} (f : P.signature.Symbol n) (t : Term P.signature n),
    P.body f = some t → Q.body (signature.symbol f) = some (t.map signature)

instance : Category.{0} Presentation where
  Hom := Hom
  id _ := ⟨𝟙 _, fun f t h => by simpa using h⟩
  comp σ τ := ⟨σ.signature ≫ τ.signature, fun f t h => by
    simpa only [Term.map_comp, Signature.Hom.symbol_comp] using τ.body _ _ (σ.body f t h)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Define a fresh function. Its body is scoped over the old signature, excluding self-calls
and forward references. -/
def define (P : Presentation) {name : Name} (fresh : P.signature.arity name = none)
    {n : Nat} (t : Term P.signature n) : Presentation where
  signature := P.signature.add name n
  body {k} f :=
    if h : f.val = name then
      have arity : n = k := Option.some.inj (by simpa [Signature.add, h] using f.property)
      some (arity ▸ t.map (Signature.addInclusion fresh n))
    else
      let old : P.signature.Symbol k := ⟨f.val, by simpa [Signature.add, h] using f.property⟩
      (P.body old).map (Term.map (Signature.addInclusion fresh n))

theorem define_body_old (P : Presentation) {name : Name} (fresh : P.signature.arity name = none)
    {n : Nat} (t : Term P.signature n) {k : Nat} (f : P.signature.Symbol k) :
    (P.define fresh t).body ((Signature.addInclusion fresh n).symbol f) =
      (P.body f).map (Term.map (Signature.addInclusion fresh n)) := by
  simp [define, Signature.Hom.symbol, Signature.ne_of_fresh fresh f]

def defineHom (P : Presentation) {name : Name} (fresh : P.signature.arity name = none)
    {n : Nat} (t : Term P.signature n) : P ⟶ P.define fresh t :=
  ⟨Signature.addInclusion fresh n, fun f _ h =>
    (define_body_old P fresh t f).trans (congrArg (Option.map (Term.map _)) h)⟩

end Presentation

/-- World snapshots retain the definition environment and the statements of named theorems. -/
structure World where
  presentation : Presentation
  theoremAt : Name → Option (Sentence presentation.signature)

namespace World

abbrev signature (W : World) := W.presentation.signature

def bare (S : Signature) : World := ⟨Presentation.bare S, fun _ => none⟩

def initial : World := bare Signature.empty

abbrev Fresh (W : World) (name : Name) : Prop :=
  W.signature.arity name = none ∧ W.theoremAt name = none

def theorems (W : World) : Set (Sentence W.signature) :=
  {p | ∃ name, W.theoremAt name = some p}

def theory (W : World) : Set (Sentence W.signature) := W.presentation.equations ∪ W.theorems

def Provable (W : World) (p : Sentence W.signature) : Prop := W.presentation.Derives W.theorems p

/-- Each named theorem has a derivation from the defining equations alone. -/
def Checked (W : World) : Prop := ∀ p ∈ W.theorems, Derives W.presentation.equations p

theorem Checked.discharge {W : World} (h : W.Checked) {p : Sentence W.signature}
    (proof : W.Provable p) : Derives W.presentation.equations p :=
  proof.bind fun q hq => hq.elim Derives.hyp (h q)

def Models (W : World) (M : Model W.signature) : Prop := ∀ p ∈ W.theory, p.Holds M

def Entails (W : World) (p : Sentence W.signature) : Prop := ∀ M, W.Models M → p.Holds M

/-- The named theorems are consequences of the defining equations. An imported starting
snapshot must establish this property separately if it already contains theorems. -/
def Valid (W : World) : Prop := ∀ M, W.presentation.Models M → W.Models M

def define (W : World) {name : Name} (fresh : W.Fresh name) {n : Nat}
    (body : Term W.signature n) : World :=
  ⟨W.presentation.define fresh.1 body,
    fun f => (W.theoremAt f).map (Sentence.map (Signature.addInclusion fresh.1 n))⟩

def addTheorem (W : World) (name : Name) (_fresh : W.Fresh name) (p : Sentence W.signature)
    (_proof : W.Provable p) : World :=
  ⟨W.presentation, fun f => if f = name then some p else W.theoremAt f⟩

/-- A world extension preserves named definitions and named theorems. -/
structure Extension (W V : World) where
  presentation : W.presentation ⟶ V.presentation
  theoremAt : ∀ name p, W.theoremAt name = some p →
    V.theoremAt name = some (p.map presentation.signature)

def Extension.id (W : World) : W.Extension W :=
  ⟨𝟙 _, fun name p h => by
    change W.theoremAt name = some (p.map (𝟙 W.signature))
    simpa using h⟩

def Extension.comp {W V U : World} (e : W.Extension V) (f : V.Extension U) : W.Extension U :=
  ⟨e.presentation ≫ f.presentation, fun name p h => by
    change U.theoremAt name = some (p.map (e.presentation.signature ≫ f.presentation.signature))
    simpa only [Sentence.map_comp] using f.theoremAt name _ (e.theoremAt name p h)⟩

end World

/-- Checked events distinguish fresh definitions from named theorems with derivations.
Theorem entries leave the function declarations and definitions unchanged. -/
inductive Event : World → World → Type
  | defun {W : World} {name : Name} (fresh : W.Fresh name) {n : Nat}
      (body : Term W.signature n) : Event W (W.define fresh body)
  | defthm {W : World} {name : Name} (fresh : W.Fresh name)
      (p : Sentence W.signature) (proof : W.Provable p) : Event W (W.addTheorem name fresh p proof)

def Event.extension {W V : World} (e : Event W V) : W.Extension V :=
  match e with
  | .defun fresh t => ⟨W.presentation.defineHom fresh.1 t, fun f p h => by
      simp [World.define, Presentation.defineHom, h]⟩
  | .defthm (name := name) fresh p proof => ⟨𝟙 _, fun f q h => by
      have different : f ≠ name := by rintro rfl; rw [fresh.2] at h; contradiction
      change (W.addTheorem name fresh p proof).theoremAt f = some (q.map (𝟙 W.signature))
      simpa [World.addTheorem, different] using h⟩

/-- A book consists of ordered, checked events relative to its input world. Its type records
both the required starting world and the resulting world. -/
inductive Book : World → World → Type
  | nil (W : World) : Book W W
  | cons {W V U : World} (head : Event W V) (tail : Book V U) : Book W U

/-- A checked book gives a world extension, including preservation of all named entries. -/
def Book.extension {W V : World} (b : Book W V) : W.Extension V :=
  match b with
  | .nil _ => World.Extension.id W
  | .cons e rest => e.extension.comp rest.extension

/-- Logical inclusion composes a checked book with the checked events already loaded.
File lookup, certification and compatibility with a different starting world are external. -/
def Book.includeBook {W V U : World} (loaded : Book W V) (book : Book V U) : Book W U :=
  match loaded with
  | .nil _ => book
  | .cons e rest => .cons e (rest.includeBook book)

end Silmaril.Logic.ACL2
