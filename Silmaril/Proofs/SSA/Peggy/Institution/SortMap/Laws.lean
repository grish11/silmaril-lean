module

public import Silmaril.SSA.Peggy.Institution.SortMap.Defs

public section

namespace Silmaril.SSA.Peggy.SortMap.Proofs

open CategoryTheory
open PEG (Ty ProfileMap)
open Dialect (FixedSortSignature OpenGraph)
open RVSDG (Tuple)

universe u v w

variable {S T U V : Signature.{u,v}}

private theorem opcode_cast {D : Type u} {P : PEG.InstructionSet.{u,v} D}
    {a b : List (Ty D)} {x y : Ty D} (ha : a = b) (hx : x = y)
    {p : P a x} {q : P b y} (h : HEq p q)
    {E : Type u} {Q : PEG.InstructionSet.{u,v} E} {f : D → E} (op : ProfileMap f P Q) :
    HEq (op p) (op q) := by
  subst b y
  cases h
  rfl

theorem hom_id_comp (f : Hom S T) : (Hom.id S).comp f = f := by
  cases f with
  | mk sorts opcode =>
    apply congrArg (Hom.mk sorts)
    funext ts t x
    apply eq_of_heq
    exact (cast_heq _ _).trans
      (opcode_cast (Ty.mapProfile_id ts) (Ty.mapData_id t) (cast_heq _ _) opcode)

theorem hom_comp_id (f : Hom S T) : f.comp (Hom.id T) = f := by
  cases f with
  | mk sorts opcode =>
    apply congrArg (Hom.mk sorts)
    funext ts t x
    exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))

theorem hom_assoc (f : Hom S T) (g : Hom T U) (h : Hom U V) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  apply congrArg (Hom.mk (h.sorts ∘ g.sorts ∘ f.sorts))
  funext ts t x
  apply eq_of_heq
  exact (cast_heq _ _).trans ((opcode_cast
    (Ty.mapProfile_comp f.sorts g.sorts ts).symm (Ty.mapData_comp f.sorts g.sorts t).symm
    (cast_heq _ _) h.opcode).trans ((cast_heq _ _).trans (cast_heq _ _)).symm)

theorem fixed_comp {D : Type u} {A B C : FixedSortSignature.{u,v} D} (f : A ⟶ B) (g : B ⟶ C) :
    Hom.ofFixed (f ≫ g) = (Hom.ofFixed f).comp (Hom.ofFixed g) := by
  apply congrArg (Hom.mk (S := .ofFixed A) (T := .ofFixed C) id)
  funext ts t x
  apply eq_of_heq
  have advance {ins ins' : List (Ty D)} {out out' : Ty D} (hs : ins = ins') (ht : out = out')
      {a : B.ops ins out} {b : B.ops ins' out'} (he : HEq a b) :
      HEq (FixedSortSignature.opcodeMap g a) (FixedSortSignature.opcodeMap g b) := by
    subst ins' out'
    cases he
    rfl
  exact (cast_heq _ _).trans
    ((cast_heq _ _).trans ((cast_heq _ _).trans
      (advance (Ty.mapProfile_id ts) (Ty.mapData_id t) (cast_heq _ _)))).symm

private theorem open_heq {D : Type u} {P : PEG.InstructionSet.{u,v} D}
    {ps ps' rs rs' : List (Ty D)} {n l : Nat} {forest : PEG.LoopForest l}
    (hp : ps = ps') (hr : rs = rs')
    {a : OpenGraph P ps rs n forest} {b : OpenGraph P ps' rs' n forest}
    (h : HEq a.graph b.graph) : HEq a b := by
  subst ps' rs'
  obtain ⟨ag, af, aw⟩ := a
  obtain ⟨bg, bf, bw⟩ := b
  cases h
  rfl

private theorem equation_eq {D : Type u} {A : FixedSortSignature.{u,v} D}
    {a b : Dialect.Equation A} (hp : a.params = b.params) (hr : a.results = b.results)
    (hl : a.loops = b.loops) (hf : HEq a.forest b.forest)
    (hln : a.leftNodes = b.leftNodes) (hrn : a.rightNodes = b.rightNodes)
    (ha : HEq a.lhs b.lhs) (hb : HEq a.rhs b.rhs) : a = b := by
  obtain ⟨ap, ar, al, af, aln, arn, a₁, a₂⟩ := a
  obtain ⟨bp, br, bl, bf, bln, brn, b₁, b₂⟩ := b
  cases hp
  cases hr
  cases hl
  cases hln
  cases hrn
  cases hf
  cases ha
  cases hb
  rfl

theorem equation_fixed {D : Type u} {A B : FixedSortSignature.{u,v} D}
    (f : A ⟶ B) (e : Dialect.Equation A) :
    Equation.map (Hom.ofFixed f) e = e.map f := by
  have cmp {n : Nat} (side : OpenGraph A.ops e.params e.results n e.forest) :
      HEq (mapOpenGraph (Hom.ofFixed f) side) (side.map (FixedSortSignature.opcodeMap f)) :=
    open_heq (Ty.mapProfile_id _) (Ty.mapProfile_id _)
      (side.graph.mapData_fixed (FixedSortSignature.opcodeMap f))
  exact equation_eq (Ty.mapProfile_id _) (Ty.mapProfile_id _) rfl HEq.rfl rfl rfl (cmp e.lhs) (cmp e.rhs)

theorem equation_id (S : Signature.{u,v}) (e : Equation S) : Equation.map (Hom.id S) e = e :=
  (equation_fixed (𝟙 S.fixed) e).trans (Dialect.Equation.map_id S.fixed e)

theorem equation_comp (f : Hom S T) (g : Hom T U) (e : Equation S) :
    Equation.map (f.comp g) e = Equation.map g (Equation.map f e) := by
  have hp := Ty.mapProfile_comp f.sorts g.sorts e.params
  have hr := Ty.mapProfile_comp f.sorts g.sorts e.results
  have cmp {n : Nat} (side : OpenGraph S.ops e.params e.results n e.forest) :
      HEq (mapOpenGraph (f.comp g) side) (mapOpenGraph g (mapOpenGraph f side)) :=
    open_heq hp.symm hr.symm (side.graph.mapData_comp f.opcode g.opcode).symm
  exact equation_eq hp.symm hr.symm rfl HEq.rfl rfl rfl (cmp e.lhs) (cmp e.rhs)

private def optionEquiv {A B : Type w} (e : A ≃ B) : Option A ≃ Option B where
  toFun := Option.map e
  invFun := Option.map e.symm
  left_inv x := by cases x <;> simp
  right_inv x := by cases x <;> simp

theorem holds_map (f : Hom S T) (m : Model.{u,v,w} T) (e : Equation S) :
    (Equation.map f e).Holds m ↔ e.Holds (reduct f m) := by
  let inputs := PEG.mapDataTupleEquiv f.sorts (Ty.valueMapEquiv f.sorts m.carrier) e.params
  let outputs := PEG.mapDataTupleEquiv
    (A := fun t => Option ((reduct f m).Value t)) (B := fun t => Option (m.Value t))
    f.sorts (fun t => optionEquiv (Ty.valueMapEquiv f.sorts m.carrier t)) e.results
  have agrees (input : Tuple (reduct f m).Value e.params) (idx : PEG.Index e.loops) {n : Nat}
      (side : OpenGraph S.ops e.params e.results n e.forest) :
      (mapOpenGraph f side).observe m (inputs input) idx =
        outputs (side.observe (reduct f m) input idx) :=
    side.graph.observe_denote_mapData f.opcode m input idx _ _
  constructor
  · intro h input idx
    apply outputs.injective
    rw [← agrees input idx e.lhs, ← agrees input idx e.rhs]
    exact h (inputs input) idx
  · intro h input idx
    obtain ⟨source, rfl⟩ := inputs.surjective input
    change (mapOpenGraph f e.lhs).observe m (inputs source) idx =
      (mapOpenGraph f e.rhs).observe m (inputs source) idx
    rw [agrees source idx e.lhs, agrees source idx e.rhs, h source idx]

end Silmaril.SSA.Peggy.SortMap.Proofs
