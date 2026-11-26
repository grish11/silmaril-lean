module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Defs

/-! # Synchronized reachable states of finite feedback tables -/

@[expose] public section

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite

variable {Q K S T B : Code} (L : Table Q K S B) (R : Table Q K T B)
  (s₀ : S.Value) (t₀ : T.Value)

/-- Reachability along a single shared sequence of repeat replies. -/
inductive PairedReach : S.Value × T.Value → Prop
  | initial : PairedReach (s₀, t₀)
  | after_reply {s s' : S.Value} {t t' : T.Value} (reach : PairedReach (s, t))
      (r : K.Value) (left : L.reply s r = .inr s') (right : R.reply t r = .inr t') :
      PairedReach (s', t')

/-- A finite constructor encoding of exactly the reachable pairs, with a table
whose two coordinate projections are commuting state maps. -/
structure Cover where
  code : Code
  decode : code.Value ≃ {p // PairedReach L R s₀ t₀ p}
  table : Table Q K code B
  left_commutes : Commutes table L (fun v => (decode v).val.1)
  right_commutes : Commutes table R (fun v => (decode v).val.2)

variable {L R s₀ t₀}

def Cover.initial (C : Cover L R s₀ t₀) : C.code.Value :=
  C.decode.symm ⟨(s₀, t₀), .initial⟩

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite
