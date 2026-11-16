module

public import Silmaril.Games.AnsMap.Defs
public import Silmaril.Games.DivComp.Defs
public import Silmaril.Games.DivLTS.Defs
import Silmaril.Proofs.Games.AnsMap.Comp

/-!
# Relabelling the answers of a strategy: theorems

**Composing with the relabelling handler is relabelling** (`comp_ansH`): for any
`σ : DStrategy E F` and `k q : F.Ar q → B' q`,

  `σ.comp (DStrategy.ofHandler (ansH k)) = σ.mapAns k`,

in all three components. An interaction of a play of `σ` with a play of the handler shows the
relabelled play, up to the round in progress at the handler (a question accepted and not yet
forwarded, or an answer received and not yet returned). The handler never diverges, and the
visible play bounds both sides of an interaction, so there is no hidden chatter. An infinite
interaction grows without bound on `σ`'s side, and its visible limit is the relabelled limit.

Proofs are in `Silmaril.Proofs.Games.AnsMap`.
-/

public section

namespace Silmaril.Games

universe u

variable {E F : Sig.{u}} {B' : F.Op → Type u}

/-- **Composing with the relabelling handler is relabelling.** -/
theorem DStrategy.comp_ansH (k : (q : F.Op) → F.Ar q → B' q) (σ : DStrategy E F) :
    σ.comp (DStrategy.ofHandler (ansH k)) = σ.mapAns k :=
  Silmaril.Proofs.Games.AnsMap.comp_ansH σ

end Silmaril.Games
