module

public import Silmaril.Logic.HybridPolyadic.Thms
public import Silmaril.Logic.Matching.FixedPoint.Thms
public import Mathlib.Data.Fin.VecNotation

/-! # Marked matching models for the hybrid/polyadic translation

The target reuses actual first-order models and full 2019 fixed-point patterns.
Its nominal operations are singleton-valued; its marked definedness operation
maps each input element to the whole carrier. These are explicit constraints
on raw operation interpretations, never an assumption about formula denotation.
-/

@[expose] public section
noncomputable section
namespace Silmaril.Logic.HybridPolyadic.Matching
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Matching

inductive Operation (S : Signature) : (n : ℕ) → (Fin n → Unit) → Unit → Type
  | atom (a : S.Atom) : Operation S 0 Fin.elim0 ()
  | nominal (a : S.Nominal) : Operation S 0 Fin.elim0 ()
  | action {k} (a : S.Action k) : Operation S k (fun _ => ()) ()
  | defined : Operation S 1 (fun _ => ()) ()

abbrev matchingSignature (S : Signature) : Algebraic.ManySorted.Signature Unit := ⟨Operation S⟩

def matchingSignatureMap {S T : Signature} (f : S ⟶ T) : matchingSignature S ⟶ matchingSignature T where
  operations op := match op with
    | .atom a => .atom (f.atom a)
    | .nominal a => .nominal (f.nominal a)
    | .action a => .action (f.action _ a)
    | .defined => .defined

def matchingSignatures : Signature ⥤ Algebraic.ManySorted.Signature Unit where
  obj := matchingSignature
  map := matchingSignatureMap
  map_id _ := by apply Algebraic.ManySorted.Signature.Hom.ext; intro n inputs output op; cases op <;> rfl
  map_comp f g := by apply Algebraic.ManySorted.Signature.Hom.ext; intro n inputs output op; cases op <;> rfl

/-- A raw matching model with transparent marked-operation constraints and a point.
Names need not be distinct. No modal formula truth is a field of this structure. -/
structure Model (S : Signature) where
  base : FirstOrder.Model (matchingSignature S)
  point : base.carrier ()
  name : S.Nominal → base.carrier ()
  nominal : ∀ a args, base.operation (.nominal a) args = {name a}
  definedness : ∀ args, base.operation .defined args = Set.univ

/-- Decoding reads the actual set-valued action graph, with result as current world. -/
abbrev decode {S : Signature} (M : Model S) : HybridPolyadic.Model S where
  World := M.base.carrier ()
  relation _ a w vs := w ∈ M.base.operation (.action a) vs
  valuation a w := w ∈ M.base.operation (.atom a) (fun i => i.elim0)
  name := M.name
  point := M.point

/-- Target arrows are the same injective bounded tuple maps as decoded hybrid models.
They will also be exposed as genuine raw matching graph homomorphisms.
No invariance is claimed here for arbitrary FO/μ patterns with global quantifiers. -/
instance (S : Signature) : Category (Model S) where
  Hom M N := decode M ⟶ decode N
  id M := 𝟙 (decode M)
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

def decodeFunctor (S : Signature) : Model S ⥤ HybridPolyadic.Model S where
  obj := decode
  map h := h
  map_id _ := rfl
  map_comp _ _ := rfl

def reduct {S T : Signature} (f : S ⟶ T) (M : Model T) : Model S where
  base := FirstOrder.SignatureMap.reduct (matchingSignatureMap f) M.base
  point := M.point
  name a := M.name (f.nominal a)
  nominal a args := M.nominal (f.nominal a) args
  definedness := M.definedness

def reductFunctor {S T : Signature} (f : S ⟶ T) : Model T ⥤ Model S where
  obj := reduct f
  map h := (HybridPolyadic.reduct f).map h
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev objectContext (n : ℕ) : Fin n → Unit := fun _ => ()
abbrev Pattern (S : Signature) (n : ℕ) := FirstOrder.Pattern (matchingSignature S) (objectContext n) ()

def nominalPattern {S : Signature} {n : ℕ} (a : S.Nominal) : Pattern S n :=
  .app (.nominal a) (fun i => i.elim0)

def definedPattern {S : Signature} {n : ℕ} (p : Pattern S n) : Pattern S n :=
  .app .defined ![p]

/-- @ uses global definedness of a singleton intersection; down existentially
chooses a singleton equal to the current result. -/
def translate {S : Signature} : {n : ℕ} → Formula S n → Pattern S n
  | _, .atom a => .app (.atom a) (fun i => i.elim0)
  | _, .bot => FirstOrder.Pattern.bottom
  | _, .imp p q => .neg (.conj (translate p) (.neg (translate q)))
  | _, .nominal a => nominalPattern a
  | _, .state i => .var i
  | _, .atNom a p => definedPattern (.conj (nominalPattern a) (translate p))
  | _, .atState i p => definedPattern (.conj (.var i) (translate p))
  | _, .dia a ps => .app (.action a) (fun i => translate (ps i))
  | _, .down p => .ex () (.conj (.var 0) (translate p))

/-- All closed 2019 patterns are admitted, although the hybrid translation is
recursion-free and enters through the actual first-order base constructor. -/
abbrev Sentence (S : Signature) := FixedPoint.ClosedPattern () (matchingSignature S)

def translateFixedPoint {S : Signature} (p : Formula S 0) : Sentence S := .base (translate p)

def Sat {S : Signature} (M : Model S) (p : Sentence S) : Prop :=
  FixedPoint.PointedModel.Satisfies (FixedPoint.PointedModel.mk M.base M.point) p

/-- Every hybrid model has a nonvacuous same-carrier constrained matching expansion. -/
abbrev expand {S : Signature} (M : HybridPolyadic.Model S) : Model S where
  base :=
    { carrier := fun _ => M.World
      nonempty := fun _ => ⟨M.point⟩
      operation op := match op with
        | .atom a => fun _ => {w | M.valuation a w}
        | .nominal a => fun _ => {M.name a}
        | .action a => fun vs => {w | M.relation _ a w vs}
        | .defined => fun _ => Set.univ }
  point := M.point
  name := M.name
  nominal := fun _ _ => rfl
  definedness := fun _ => rfl

end Silmaril.Logic.HybridPolyadic.Matching
