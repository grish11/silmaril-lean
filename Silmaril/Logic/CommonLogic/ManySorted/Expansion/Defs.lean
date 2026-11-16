module

public import Silmaril.Logic.CommonLogic.ManySorted.Thms
public import Mathlib.Data.List.OfFn

/-! Tagged expansion of many-sorted FOL structures into operation-typed Common Logic models. -/
@[expose] public section
noncomputable section

namespace Silmaril.Logic.CommonLogic.ManySorted.Expansion

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples
open Silmaril.Logic.CommonLogic Silmaril.Logic.CommonLogic.ManySorted

variable {S : FOL.Signature}

/-- The extra value inhabits CL discourse even when all source carriers are empty. -/
abbrev Discourse (M : FOL.Structure S) := Unit ⊕ (Sigma M.carrier)

def junk (M : FOL.Structure S) : Discourse M := .inl ()

def tag (M : FOL.Structure S) (s : S.S) (a : M.carrier s) : Discourse M :=
  .inr ⟨s, a⟩

theorem tag_injective (M : FOL.Structure S) (s : S.S) : Function.Injective (tag M s) := by
  intro a b h
  exact eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj h)).2

/-- Encode an actual sorted tuple in the order expected by the CL application. -/
def encode (M : FOL.Structure S) {n : Nat} {w : Fin n → S.S}
    (args : ∀ i, M.carrier (w i)) : List (Discourse M) :=
  List.ofFn (fun i => tag M (w i) (args i))

theorem encode_injective (M : FOL.Structure S) {n : Nat} {w : Fin n → S.S} :
    Function.Injective (encode M (w := w)) := by
  intro a b h
  have htag := List.ofFn_injective h
  funext i
  exact tag_injective M (w i) (congrFun htag i)

/-- Typed tuple recognition specifies the profile before any choice is made. -/
def applyOperation (M : FOL.Structure S) {n : Nat} {w : Fin n → S.S} {s : S.S}
    (o : S.Op n w s) (xs : List (Discourse M)) : Discourse M := by
  classical
  exact if h : ∃ args : ∀ i, M.carrier (w i), xs = encode M args then
    tag M s (M.op o (Classical.choose h))
  else junk M

/-- Off-profile inputs use junk, never a chosen value from a source sort. -/
def function (M : FOL.Structure S) :
    (Discourse M ⊕ Head S) → List (Discourse M) → Discourse M
  | .inr (.op o), xs => applyOperation M o xs
  | _, _ => junk M

/-- Sorts and source relations are recognized only on their tagged tuples. -/
def relation (M : FOL.Structure S) :
    (Discourse M ⊕ Head S) → List (Discourse M) → Prop
  | .inr (.sort s), xs => ∃ a : M.carrier s, xs = [tag M s a]
  | .inr (.rel r), xs => ∃ args, xs = encode M args ∧ M.rel r args
  | _, _ => False

def raw (M : FOL.Structure S) : Core.Model (signature S) where
  Reference := Discourse M ⊕ Head S
  Discourse := Discourse M
  nonempty := ⟨junk M⟩
  embed := Sum.inl
  injective := Sum.inl_injective
  discourse := Empty.elim
  nondiscourse := Sum.inr
  outside _ _ := by intro h; cases h
  sequence := Empty.elim
  function := function M
  relation := relation M

/-- Exact operation behavior on tagged tuples, including arity zero. -/
theorem function_encode (M : FOL.Structure S) {n : Nat} {w : Fin n → S.S} {s : S.S}
    (o : S.Op n w s) (args : ∀ i, M.carrier (w i)) :
    (raw M).function ((raw M).nondiscourse (.op o)) (encode M args) =
      tag M s (M.op o args) := by
  classical
  let h : ∃ a, encode M args = encode M a := ⟨args, rfl⟩
  have ha : Classical.choose h = args :=
    encode_injective M (Classical.choose_spec h).symm
  change (if h : ∃ a, encode M args = encode M a then
    tag M s (M.op o (Classical.choose h)) else junk M) = _
  rw [dite_eq_left h]
  exact congrArg (fun a => tag M s (M.op o a)) ha

theorem function_off_profile (M : FOL.Structure S) {n : Nat} {w : Fin n → S.S} {s : S.S}
    (o : S.Op n w s) (xs : List (Discourse M))
    (h : ¬ ∃ args : ∀ i, M.carrier (w i), xs = encode M args) :
    (raw M).function ((raw M).nondiscourse (.op o)) xs = junk M := by
  exact dite_eq_right h

theorem relation_encode (M : FOL.Structure S) {n : Nat} {w : Fin n → S.S}
    (r : S.Rel n w) (args : ∀ i, M.carrier (w i)) :
    (raw M).relation ((raw M).nondiscourse (.rel r)) (encode M args) ↔ M.rel r args := by
  constructor
  · rintro ⟨a, ha, hr⟩
    have same : a = args := encode_injective M ha.symm
    exact same ▸ hr
  · intro hr
    exact ⟨args, rfl, hr⟩

theorem raw_wellTyped (M : FOL.Structure S) : WellTyped (raw M) := by
  intro n w s o xs hx
  have inhabited : ∀ i, ∃ a : M.carrier (w i), xs i = tag M (w i) a := by
    intro i
    obtain ⟨a, ha⟩ := hx i
    exact ⟨a, List.singleton_inj.mp ha⟩
  let args : ∀ i, M.carrier (w i) := fun i => Classical.choose (inhabited i)
  have hxs : xs = fun i => tag M (w i) (args i) :=
    funext (fun i => Classical.choose_spec (inhabited i))
  change ∃ a : M.carrier s,
    [(raw M).function ((raw M).nondiscourse (.op o)) (List.ofFn xs)] = [tag M s a]
  refine ⟨M.op o args, ?_⟩
  rw [hxs]
  exact congrArg (fun x => [x]) (function_encode M o args)

/-- An object expansion of every public FOL structure; no nonempty carrier assumption. -/
def expand (M : FOL.Structure S) : TypedModel S := ⟨raw M, raw_wellTyped M⟩

/-- Tagging supplies an element of precisely the decoded source sort. -/
def pack (M : FOL.Structure S) (s : S.S) (a : M.carrier s) :
    (decode (expand M)).carrier s := ⟨tag M s a, a, rfl⟩

/-- The sort predicate itself supplies the inverse witness. -/
def unpack (M : FOL.Structure S) {s : S.S} (x : (decode (expand M)).carrier s) :
    M.carrier s := Classical.choose x.property

theorem unpack_spec (M : FOL.Structure S) {s : S.S} (x : (decode (expand M)).carrier s) :
    x.val = tag M s (unpack M x) :=
  List.singleton_inj.mp (Classical.choose_spec x.property)

theorem unpack_pack (M : FOL.Structure S) (s : S.S) (a : M.carrier s) :
    unpack M (pack M s a) = a :=
  tag_injective M s (unpack_spec M (pack M s a)).symm

theorem pack_unpack (M : FOL.Structure S) {s : S.S} (x : (decode (expand M)).carrier s) :
    pack M s (unpack M x) = x :=
  Subtype.ext (unpack_spec M x).symm

def carrierEquiv (M : FOL.Structure S) (s : S.S) :
    (decode (expand M)).carrier s ≃ M.carrier s where
  toFun := unpack M
  invFun := pack M s
  left_inv := pack_unpack M
  right_inv := unpack_pack M s

end Silmaril.Logic.CommonLogic.ManySorted.Expansion
