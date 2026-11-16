module

public import Silmaril.Games.Zip.Defs
public import Mathlib.Data.Set.Defs

/-!
# Hidden chatter of two traces

`Chatter I J p` says that the two traces `I` (over `α ⊕ β`) and `J` (over
`β ⊕ γ`), each given by its set of finite prefixes, interact forever while the
visible trace stays `p`: arbitrarily long members of `I` and `J` synchronise on
the shared alphabet `β` with visible part `p`.

So both traces are infinite, their outer (`α` and `γ`) events are eventually
constant, the outer events being those of `p`, and their shared events agree.
This is the shape of hidden chatter in a composite of divergence-observing
strategies (`Silmaril.Games.DivCompChatter.Thms`).
-/

@[expose] public section

namespace Silmaril.Games

universe u v w

/-- `I` and `J` chatter after `p`: arbitrarily long members of `I` and `J`
interact with visible part `p`. -/
def Chatter {α : Type u} {β : Type v} {γ : Type w} (I : Set (List (α ⊕ β)))
    (J : Set (List (β ⊕ γ))) (p : List (α ⊕ γ)) : Prop :=
  ∀ k, ∃ s ∈ I, ∃ t ∈ J, k ≤ s.length + t.length ∧ Zip s t p

end Silmaril.Games
