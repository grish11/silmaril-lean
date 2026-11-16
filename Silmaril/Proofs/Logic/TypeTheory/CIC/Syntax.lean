module

public import Silmaril.Logic.TypeTheory.CIC.Syntax.Defs
import Mathlib.Tactic

public section

namespace Silmaril.Proofs.Logic.TypeTheory.CIC.SyntaxLaws

open Silmaril.Logic.TypeTheory.CIC

universe u

private theorem map_self {α : Type u} {f : α → α} {xs : List α}
    (h : ∀ x ∈ xs, f x = x) : xs.map f = xs :=
  (List.map_congr_left h).trans (List.map_id xs)

private theorem predicate_map_self {Level : Type u} (p : Predicate (Term Level) Level)
    (f : ℕ → Term Level → Term Level) (k : ℕ)
    (hp : ∀ a ∈ p.parameters, f k a = a)
    (hr : f (p.context.length + k) p.returnType = p.returnType) :
    { p with parameters := p.parameters.map (f k),
             returnType := f (p.context.length + k) p.returnType } = p := by
  have hm : p.parameters.map (f k) = p.parameters := map_self hp
  simp only [hm, hr]

private theorem branches_map_self {Level : Type u} (bs : List (Branch (Term Level)))
    (f : ℕ → Term Level → Term Level) (k : ℕ)
    (hb : ∀ b ∈ bs, f (b.context.length + k) b.body = b.body) :
    bs.map (fun b => { b with body := f (b.context.length + k) b.body }) = bs := by
  apply map_self
  intro b h
  simp only [hb b h]

private theorem fixes_map_self {Level : Type u} (ds : List (FixDef (Term Level)))
    (f : ℕ → Term Level → Term Level) (k : ℕ)
    (ht : ∀ d ∈ ds, f k d.type = d.type)
    (hb : ∀ d ∈ ds, f (ds.length + k) d.body = d.body) :
    ds.map (fun d => { d with type := f k d.type, body := f (ds.length + k) d.body }) = ds := by
  apply map_self
  intro d h
  simp only [ht d h, hb d h]

@[simp] theorem lift_zero {Level : Type u} (cutoff : ℕ) (t : Term Level) :
    t.lift 0 cutoff = t := by
  fun_induction Term.lift 0 cutoff t <;> simp_all
  case case11 k ci p c brs hp hr hc hb =>
    constructor
    · simpa only [hr] using predicate_map_self p (Term.lift 0) k hp hr
    · exact branches_map_self brs (Term.lift 0) k hb
  case case13 k ds i ht hb => exact fixes_map_self ds (Term.lift 0) k ht hb
  case case14 k ds i ht hb => exact fixes_map_self ds (Term.lift 0) k ht hb

@[simp] theorem subst_nil {Level : Type u} (cutoff : ℕ) (t : Term Level) :
    t.subst [] cutoff = t := by
  fun_induction Term.subst [] cutoff t <;> simp_all
  case case13 k ci p c brs hp hr hc hb =>
    constructor
    · simpa only [hr] using predicate_map_self p (Term.subst []) k hp hr
    · exact branches_map_self brs (Term.subst []) k hb
  case case15 k ds i ht hb => exact fixes_map_self ds (Term.subst []) k ht hb
  case case16 k ds i ht hb => exact fixes_map_self ds (Term.subst []) k ht hb

end Silmaril.Proofs.Logic.TypeTheory.CIC.SyntaxLaws
