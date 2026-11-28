module

public import Silmaril.Semantics.TrackA.Interaction.Thms
public import Mathlib.Logic.Equiv.Basic

/-! # Relabeling complete interaction observations -/

@[expose] public section

namespace Silmaril.Semantics.TrackA.Interaction

universe u v w x y z b d s i

variable {S : Signature.{u,v}} {T : Signature.{w,x}}

/-- The backward map must be bijective at each source request to relabel all
completed exchanges in both directions along a run. Requests can coalesce. -/
structure Signature.TraceHom (S : Signature.{u,v}) (T : Signature.{w,x}) where
  hom : Hom S T
  bijective (q : S.Request) : Function.Bijective (hom.response q)

def Signature.TraceHom.id (S : Signature.{u,v}) : Signature.TraceHom S S :=
  ⟨Hom.id S, fun _ => Function.bijective_id⟩

def Signature.TraceHom.comp {U : Signature.{y,z}} (g : Signature.TraceHom T U)
    (f : Signature.TraceHom S T) : Signature.TraceHom S U :=
  ⟨g.hom.comp f.hom, fun q => (f.bijective q).comp (g.bijective (f.hom.request q))⟩

/-- The forward reply map is determined by the dependent backward map. -/
noncomputable def Signature.TraceHom.reply (f : Signature.TraceHom S T) (q : S.Request) :
    S.Response q ≃ T.Response (f.hom.request q) :=
  (Equiv.ofBijective (f.hom.response q) (f.bijective q)).symm

noncomputable def Signature.TraceHom.exchange (f : Signature.TraceHom S T) :
    S.Exchange → T.Exchange :=
  fun ⟨q, r⟩ => ⟨f.hom.request q, f.reply q r⟩

variable {A : Type y} {B : Signature.{b,d}} {X : Type z} {I : Type i}

def End.relabel (f : Signature.Hom S T) : End S A → End T A
  | .returned a => .returned a
  | .stuck q => .stuck (f.request q)
  | .deadlock kind => .deadlock kind
  | .diverge => .diverge

noncomputable def Trace.relabel (f : Signature.TraceHom S T) : Trace S A → Trace T A
  | .finite es ending => .finite (es.map f.exchange) (ending.relabel f.hom)
  | .infinite es => .infinite (f.exchange ∘ es)

def Coalgebra.relabel (f : Signature.Hom S T) (c : Coalgebra S B A X) : Coalgebra T B A X :=
  fun state => (c state).relabel f

def Forest.relabel (f : Signature.Hom S T) (forest : Forest.{u,v,b,d,y,i,s} S B A I) :
    Forest.{w,x,b,d,y,i,s} T B A I where
  State := forest.State
  unfold := forest.unfold.relabel f
  root := forest.root

end Silmaril.Semantics.TrackA.Interaction
