module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Provenance.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Scoped.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.Provenance

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback
open LambdaSSA (Flat Tm)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (Primitive region term)
open Silmaril.Elgot.ITree (Tree diverge diverge_bind)

universe u v w
variable {Events : Type w → Type w} {α β A B : Type u} {F : Type v}

private theorem bind_codec {x : Tree Events α} {y : Tree Events β} {f : α → β} {g : A → B}
    {l : α → Tree Events A} {r : β → Tree Events B}
    (same : f <$> x = y) (next : ∀ a, g <$> l a = r (f a)) :
    g <$> (x >>= l) = y >>= r := by
  rw [← same, map_bind]
  simp only [← bind_pure_comp, bind_assoc, pure_bind]
  exact bind_congr next

variable {left : Primitive Events F α} {right : Primitive Events F β} {atom : α → β}

local notation "codec" => valueCodec atom

private theorem extend_codec (env : Env α) (v : Value α) :
    codec ∘ extend env v = extend (codec ∘ env) (codec v) := by
  funext i
  cases i <;> rfl

private theorem term_codec (h : PrimitivesAgree left right atom) (env : Env α) (t : Tm F) :
    codec <$> term left env t = term right (codec ∘ env) t := by
  induction t generalizing env with
  | var i => exact map_pure _ _
  | unit => exact map_pure _ _
  | op op arg ih =>
    simp only [term]
    exact bind_codec (ih env) (h op)
  | pair a b iha ihb =>
    simp only [term]
    refine bind_codec (iha env) fun x => bind_codec (ihb env) fun y => ?_
    exact map_pure _ _
  | let₁ a b iha ihb =>
    simp only [term]
    exact bind_codec (iha env) fun v => (ihb (extend env v)).trans
      (congrArg (fun e => term right e b) (extend_codec env v))
  | let₂ a b iha ihb =>
    simp only [term]
    apply bind_codec (iha env)
    intro value
    cases value <;> simp only [valueCodec, map_eq_pure_bind, diverge_bind]
    simpa only [← map_eq_pure_bind, extend_codec] using ihb (extend (extend env _) _)
  | inl a ih | inr a ih =>
    simp only [term]
    exact bind_codec (ih env) fun v => map_pure _ _
  | case a l r iha ihl ihr =>
    simp only [term]
    apply bind_codec (iha env)
    intro value
    cases value <;> simp only [valueCodec, map_eq_pure_bind, diverge_bind]
    · simpa only [← map_eq_pure_bind, extend_codec] using ihl (extend env _)
    · simpa only [← map_eq_pure_bind, extend_codec] using ihr (extend env _)
  | abort a ih =>
    simp only [term]
    exact bind_codec (ih env) fun _ => by simp only [map_eq_pure_bind, diverge_bind]

theorem flat_codec {labels n : Nat} (h : PrimitivesAgree left right atom)
    (row : Flat F labels n) (env : Env α) :
    resultCodec atom <$> region left env row.erase = region right (codec ∘ env) row.erase := by
  induction row generalizing env with
  | br i a =>
    simp only [Flat.erase, region]
    exact bind_codec (term_codec h env _) fun v => map_pure _ _
  | let₁ a b ih =>
    simp only [Flat.erase, region]
    exact bind_codec (term_codec h env _) fun v => (ih (extend env v)).trans
      (congrArg (fun e => region right e b.erase) (extend_codec env v))
  | let₂ a b ih =>
    simp only [Flat.erase, region]
    apply bind_codec (term_codec h env _)
    intro value
    cases value <;> simp only [valueCodec, map_eq_pure_bind, diverge_bind]
    simpa only [← map_eq_pure_bind, extend_codec] using ih (extend (extend env _) _)
  | case a l r ihl ihr =>
    simp only [Flat.erase, region]
    apply bind_codec (term_codec h env _)
    intro value
    cases value <;> simp only [valueCodec, map_eq_pure_bind, diverge_bind]
    · simpa only [← map_eq_pure_bind, extend_codec] using ihl (extend env _)
    · simpa only [← map_eq_pure_bind, extend_codec] using ihr (extend env _)

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.Provenance
