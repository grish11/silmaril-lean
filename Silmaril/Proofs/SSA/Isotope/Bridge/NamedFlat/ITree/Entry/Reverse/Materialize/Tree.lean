module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Materialize.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.FlatLetCase.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Support.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize
open LambdaSSA (FiniteCFG Flat)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (Primitive region term)
open LetCase.LocallyNameless (Tm)
open Morphism.CaseSSA (erase erase_rename)

universe u v w
variable {Events : Type u → Type u} {F : Type v} {α : Type w} {labels blocks exits n : Nat}

private theorem jump_tree (raw : Primitive Events F α) (env : Env α)
    (canBind : Bool) (target : Fin labels) (arg : Tm Empty F n) :
    region raw env (jump canBind target arg).erase = region raw env (Flat.br target arg).erase := by
  cases arg <;> try rfl
  case let₁ a tail =>
    cases canBind with
    | true => simp [jump, Flat.erase, region, erase, term]
    | false =>
      cases a <;> try rfl
      case bv i =>
        simp only [jump, Bool.false_eq_true, ↓reduceIte, Flat.erase, region, erase, term, pure_bind]
        rw [LambdaSSA.Acyclic.FlatLetCase.operand_rename_tree raw (aliasIndex i)
          (env := extend env (env i.val)) (env' := env) (Fin.cases rfl fun _ => rfl)]

private theorem body_tree (raw : Primitive Events F α) (t : Flat F labels n)
    (canBind : Bool) (env : Env α) :
    region raw env (body canBind t).erase = region raw env t.erase := by
  induction t generalizing env canBind with
  | br i a => exact jump_tree raw env canBind i a
  | let₁ a t ih | let₂ a t ih =>
    simp only [body, Flat.erase, region, ih]
  | case a l r left right =>
    simp only [body, Flat.erase, region, left, right]

theorem graph_tree (raw : Primitive Events F α) (g : FiniteCFG F blocks exits n) (env : Env α) :
    region raw env (graph g).erase = region raw env g.erase := by
  simp only [graph, FiniteCFG.erase, region, body_tree]

private theorem alias_scoped (i : Fin n) (tail : Tm Empty F (n + 1)) {bound : Nat}
    (inside : i.val < bound) (s : (erase tail).Scoped (bound + 1)) :
    (erase (tail.rename (aliasIndex i))).Scoped bound := by
  let ren : Nat → Nat
    | 0 => i.val
    | j + 1 => j
  have agrees (j : Fin (n + 1)) : (aliasIndex i j).val = ren j.val :=
    Fin.cases rfl (fun _ => rfl) j
  rw [erase_rename _ ren agrees, LambdaSSA.Tm.scoped_iff_usesVar_lt]
  intro j used
  obtain ⟨older, found, eq⟩ := (LambdaSSA.Tm.usesVar_rename (erase tail) ren j).mp used
  have inScope := (LambdaSSA.Tm.scoped_iff_usesVar_lt _ _).mp s older found
  cases older with
  | zero => exact eq ▸ inside
  | succ k =>
    change k = j at eq
    omega

private theorem jump_scoped (canBind : Bool) (target : Fin labels) (arg : Tm Empty F n)
    {bound : Nat} (s : (erase arg).Scoped bound) :
    (jump canBind target arg).erase.Scoped labels bound := by
  cases arg <;> try exact ⟨target.isLt, s⟩
  case let₁ a tail =>
    cases canBind with
    | true => exact ⟨s.1, target.isLt, s.2⟩
    | false =>
      cases a <;> try exact ⟨target.isLt, s⟩
      case bv i => exact ⟨target.isLt, alias_scoped i tail s.1 s.2⟩

theorem body_scoped (t : Flat F labels n) (canBind : Bool) {bound : Nat}
    (s : t.erase.Scoped labels bound) : (body canBind t).erase.Scoped labels bound := by
  induction t generalizing canBind bound with
  | br i a => exact jump_scoped canBind i a s.2
  | let₁ a t ih | let₂ a t ih => exact ⟨s.1, ih canBind s.2⟩
  | case a l r left right => exact ⟨s.1, left false s.2.1, right false s.2.2⟩

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize
