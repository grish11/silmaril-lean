module

public import Silmaril.SSA.Peggy.Institution.SortMap.Defs
import Silmaril.Proofs.SSA.Peggy.Institution.SortMap.Laws

/-! # The Peggy institution with variable data sorts -/

@[expose] public section

namespace Silmaril.SSA.Peggy.SortMap

open CategoryTheory

universe u v w

variable {S T U V : Signature.{u,v}}

theorem Hom.id_comp (f : Hom S T) : (Hom.id S).comp f = f := Proofs.hom_id_comp f

theorem Hom.comp_id (f : Hom S T) : f.comp (Hom.id T) = f := Proofs.hom_comp_id f

theorem Hom.assoc (f : Hom S T) (g : Hom T U) (h : Hom U V) :
    (f.comp g).comp h = f.comp (g.comp h) := Proofs.hom_assoc f g h

instance : Category.{max u v} Signature.{u,v} where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

@[simp] theorem Equation.map_id (S : Signature.{u,v}) (e : Equation S) :
    Equation.map (𝟙 S) e = e := Proofs.equation_id S e

theorem Equation.map_comp (f : S ⟶ T) (g : T ⟶ U) (e : Equation S) :
    Equation.map (f ≫ g) e = Equation.map g (Equation.map f e) := Proofs.equation_comp f g e

@[simp] theorem reduct_id (S : Signature.{u,v}) (m : Model.{u,v,w} S) :
    reduct (𝟙 S) m = m := m.reductData_fixed (fun x => x)

theorem reduct_comp (f : S ⟶ T) (g : T ⟶ U) (m : Model.{u,v,w} U) :
    reduct (f ≫ g) m = reduct f (reduct g m) := m.reductData_comp f.opcode g.opcode

/-- Exact satisfaction of open equations under sort and opcode translation. -/
theorem Equation.holds_map (f : S ⟶ T) (m : Model.{u,v,w} T) (e : Equation S) :
    (Equation.map f e).Holds m ↔ e.Holds (reduct f m) := Proofs.holds_map f m e

def plain : Silmaril.Inst.Plain.{max (u + 1) (v + 1), max u v, max u v, max u v (w + 1)}
    Signature.{u,v} where
  Sen := Equation
  map := Equation.map
  map_id := Equation.map_id
  map_comp := Equation.map_comp
  Mod := Model.{u,v,w}
  reduct := reduct
  reduct_id := reduct_id
  reduct_comp := reduct_comp
  Sat m e := e.Holds m
  sat_map := Equation.holds_map

-- The result type of toInst combines these levels, but the signature and
-- carrier types in its construction retain the three independent choices.
set_option linter.checkUnivs false in
abbrev inst := plain.{u,v,w}.toInst

open Dialect (FixedSortSignature)

theorem Hom.ofFixed_comp {D : Type u} {A B C : FixedSortSignature.{u,v} D}
    (f : A ⟶ B) (g : B ⟶ C) :
    Hom.ofFixed (f ≫ g) = (Hom.ofFixed f).comp (Hom.ofFixed g) := Proofs.fixed_comp f g

def fixedSignature (D : Type u) : FixedSortSignature.{u,v} D ⥤ Signature.{u,v} where
  obj := Signature.ofFixed
  map := Hom.ofFixed
  map_id _ := rfl
  map_comp := Hom.ofFixed_comp

theorem map_fixed {D : Type u} {A B : FixedSortSignature.{u,v} D}
    (f : A ⟶ B) (e : Dialect.Equation A) :
    Equation.map (Hom.ofFixed f) e = e.map f := Proofs.equation_fixed f e

theorem reduct_fixed {D : Type u} {A B : FixedSortSignature.{u,v} D}
    (f : A ⟶ B) (m : Institution.Model.{u,v,w} B) :
    reduct (Hom.ofFixed f) m = Institution.reduct f m :=
  m.reductData_fixed (FixedSortSignature.opcodeMap f)

/-- The fixed-sort institution embeds with its original sentences, models and satisfaction. -/
def fixedComparison (D : Type u) :
    Silmaril.Inst.Comorphism (Institution.inst.{u,v,w} D) inst.{u,v,w} :=
  Silmaril.Inst.Comorphism.ofPlain (P := Institution.plain D) (Q := plain) (fixedSignature D)
    (fun _ e => e) (fun _ m => m) (fun _ _ _ => Iff.rfl)
    (fun f e => (map_fixed f e).symm) (fun f m => (reduct_fixed f m).symm)

end Silmaril.SSA.Peggy.SortMap
