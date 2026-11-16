module

public import Silmaril.Logic.CommonLogic.Core.FirstOrder.Defs
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

@[expose] public section

namespace Silmaril.Logic.CommonLogic.ManySorted

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples
open Silmaril.Logic.CommonLogic

/-- Complete profiles distinguish heads; the source signature and its sorts are unrestricted. -/
inductive Head (S : FOL.Signature) where
  | sort (s : S.S)
  | op {n : Nat} {w : Fin n → S.S} {s : S.S} (o : S.Op n w s)
  | rel {n : Nat} {w : Fin n → S.S} (r : S.Rel n w)

abbrev signature (S : FOL.Signature) : Core.Signature := ⟨Empty, Head S, Empty⟩

def signatureMap {S T : FOL.Signature} (f : S ⟶ T) : signature S ⟶ signature T :=
  ⟨Empty.elim, fun h => match h with
    | .sort s => .sort (f.sorts s)
    | .op o => .op (f.ops o)
    | .rel r => .rel (f.rels r), Empty.elim⟩

private theorem signatureHom_ext {S T : Core.Signature} (f g : S ⟶ T)
    (hd : f.discourse = g.discourse) (hn : f.nondiscourse = g.nondiscourse)
    (hm : f.marker = g.marker) : f = g := by
  cases f; cases g; cases hd; cases hn; cases hm; rfl

@[simp] theorem signatureMap_id (S : FOL.Signature) :
    signatureMap (𝟙 S) = 𝟙 (signature S) := by
  apply signatureHom_ext
  · funext x; exact Empty.elim x
  · funext h; cases h <;> rfl
  · funext x; exact Empty.elim x

@[simp] theorem signatureMap_comp {S T U : FOL.Signature} (f : S ⟶ T) (g : T ⟶ U) :
    signatureMap (f ≫ g) = signatureMap f ≫ signatureMap g := by
  apply signatureHom_ext
  · funext x; exact Empty.elim x
  · funext h; cases h <;> rfl
  · funext x; exact Empty.elim x

def signatures : FOL.Signature ⥤ Core.Signature where
  obj := signature
  map := signatureMap
  map_id := signatureMap_id
  map_comp := signatureMap_comp

abbrev tuple := @Core.FirstOrder.tuple

/-- Membership in a source sort is a unary CL predicate, not a global partition. -/
def guard {S : FOL.Signature} {n k : Nat} (s : S.S)
    (t : Core.Expr (signature S) n k .individual) : Core.Formula (signature S) n k :=
  .pred (.nonname (.sort s)) (.cons t .nil)

/-- Conjunction of all input-sort guards; the empty tuple has guard true. -/
def guards {S : FOL.Signature} {n k : Nat} : {m : Nat} → (Fin m → S.S) →
    (Fin m → Core.Expr (signature S) n k .individual) → Core.Formula (signature S) n k
  | 0, _, _ => .tt
  | _+1, w, ts => .conj (guard (w 0) (ts 0))
      (guards (fun i => w i.succ) (fun i => ts i.succ))

/-- Universal closure over the individual context; no sequence binders are introduced. -/
def close {S : Core.Signature} : {n : Nat} → Core.Formula S n 0 → Core.Sentence S
  | 0, p => p
  | _+1, p => close (.all p)

/-- Operation closure, including constants. It makes no assertion about off-sort applications. -/
def typingAxiom {S : FOL.Signature} {n : Nat} {w : Fin n → S.S} {s : S.S}
    (o : S.Op n w s) : Core.Sentence (signature S) :=
  close (.impl (guards w (fun i => .var i))
    (guard s (.app (.nonname (.op o)) (tuple (fun i => .var i)))))

/-- No nonemptiness, disjointness, exhaustiveness, or relation-typing axioms are added. -/
def typingTheory (S : FOL.Signature) : Set (Core.Sentence (signature S)) :=
  {p | ∃ n w s, ∃ (o : S.Op n w s), p = typingAxiom o}

/-- Semantic operation closure, used to construct the typed decoder without choosing fillers. -/
def WellTyped {S : FOL.Signature} (M : Core.Model (signature S)) : Prop :=
  ∀ {n : Nat} {w : Fin n → S.S} {s : S.S} (o : S.Op n w s)
    (xs : Fin n → M.Discourse),
    (∀ i, M.relation (M.nondiscourse (.sort (w i))) [xs i]) →
    M.relation (M.nondiscourse (.sort s))
      [M.function (M.nondiscourse (.op o)) (List.ofFn xs)]

/-- The typing property discards no arrows between retained CL models. -/
def typed (S : FOL.Signature) : ObjectProperty (Core.Model (signature S)) := WellTyped

abbrev TypedModel (S : FOL.Signature) := (typed S).FullSubcategory

/-- Typing closure pulls back along arbitrary signature maps, even when sorts are identified. -/
def typedReduct {S T : FOL.Signature} (f : S ⟶ T) : TypedModel T ⥤ TypedModel S :=
  (typed S).lift ((typed T).ι ⋙ Core.Model.reduct (signatureMap f))
    (fun M {_ _ _} o xs hx => M.property (f.ops o) xs hx)

abbrev carrier {S : FOL.Signature} (M : Core.Model (signature S)) (s : S.S) :=
  {x : M.Discourse // M.relation (M.nondiscourse (.sort s)) [x]}

/-- Empty predicates decode as empty carriers. Operation typing supplies the output witness. -/
abbrev decode {S : FOL.Signature} (M : TypedModel S) : FOL.Structure S where
  carrier := carrier M.obj
  op o xs := ⟨M.obj.function (M.obj.nondiscourse (.op o)) (List.ofFn (fun i => (xs i).val)),
    M.property o (fun i => (xs i).val) (fun i => (xs i).property)⟩
  rel r xs := M.obj.relation (M.obj.nondiscourse (.rel r)) (List.ofFn (fun i => (xs i).val))

/-- Sort guards and function commutation restrict every actual CL model homomorphism. -/
def decodeHom {S : FOL.Signature} {M N : TypedModel S} (h : M ⟶ N) : decode M ⟶ decode N where
  map s x := ⟨h.hom.discourse x.val, by
    have hx := h.hom.relation (M.obj.nondiscourse (.sort s)) [x.val] x.property
    simpa only [h.hom.nonname, List.map_cons, List.map_nil] using hx⟩
  map_op o xs := by
    apply Subtype.ext
    simpa only [decode, h.hom.nonname, List.map_ofFn, Function.comp_def] using
      h.hom.function (M.obj.nondiscourse (.op o)) (List.ofFn (fun i => (xs i).val))
  map_rel r xs hr := by
    have hh := h.hom.relation _ _ hr
    simpa only [decode, h.hom.nonname, List.map_ofFn, Function.comp_def] using hh

def models (S : FOL.Signature) : TypedModel S ⥤ FOL.Structure S where
  obj := decode
  map := decodeHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Erase typing into finite named-head applications. -/
def term {S : FOL.Signature} {n k : Nat} {Γ : Fin n → S.S} :
    {s : S.S} → EQ.Term S.toSignature Γ s → Core.Expr (signature S) n k .individual
  | _, .var i => .var i
  | _, .app o args => .app (.nonname (.op o)) (tuple (fun i => term (args i)))

/-- Quantifiers range over exactly the source sort predicate, including when it is empty. -/
def formula {S : FOL.Signature} : {n k : Nat} → {Γ : Fin n → S.S} →
    FOL.Formula S Γ → Core.Formula (signature S) n k
  | _, _, _, .eq t u => .equal (term t) (term u)
  | _, _, _, .rel r args => .pred (.nonname (.rel r)) (tuple (fun i => term (args i)))
  | _, _, _, .tt => .tt
  | _, _, _, .not p => .neg (formula p)
  | _, _, _, .and p q => .conj (formula p) (formula q)
  | _, _, _, .all (Δ := Δ) _ p => .all (.impl (guard (Δ 0) (.var 0)) (formula p))

def sentence {S : FOL.Signature} (p : FOL.Sentence S) : Core.Sentence (signature S) :=
  formula p.formula

end Silmaril.Logic.CommonLogic.ManySorted
