module

public import Silmaril.Logic.TypeTheory.LambdaPi.Eta.Thms
public import Silmaril.Logic.TypeTheory.LambdaPi.Generation.Thms
import Silmaril.Proofs.Logic.TypeTheory.LambdaPi.EtaTyping

@[expose] public section

namespace Silmaril.Logic.TypeTheory.LambdaPi

/-- Weakening beneath a binder and applying its fresh variable cancel. -/
theorem Term.codomain_fresh (B : Term) :
    (B.rename (Silmaril.DeBruijn.lift Nat.succ)).substOne (.var 0) = B :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.EtaTyping.codomain_fresh B

/-- Apply an actually typed dependent function to the fresh variable.
The codomain is the original dependent body, without an extra renaming.
-/
theorem Derives.etaApplication {C : Calculus} {Γ : List Term} {f A B : Term}
    (hf : Derives C ∅ ⟨Γ, f, .pi A B⟩) :
    Derives C ∅ ⟨A :: Γ, .app (f.rename Nat.succ) (.var 0), B⟩ :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.EtaTyping.application_typed hf

/-- η expansion preserves an actual dependent function type, including in open contexts.
This holds in the original calculus, before adding the η conversion schema.
-/
theorem Derives.etaExpansion {C : Calculus} {Γ : List Term} {f A B : Term}
    (hf : Derives C ∅ ⟨Γ, f, .pi A B⟩) :
    Derives C ∅ ⟨Γ, .lam A (.app (f.rename Nat.succ) (.var 0)), .pi A B⟩ :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.EtaTyping.expansion_typed hf

/-- In the η extension, conversion of functions is equivalent to conversion
of their applications to the fresh variable. For a typed dependent function,
`etaApplication` and `etaExpansion` give the actual endpoint typings.
-/
theorem Calculus.withEta_conversion_iff_pointwise (C : Calculus) (f g : Term) :
    C.withEta.Conversion f g ↔
      C.withEta.Conversion (.app (f.rename Nat.succ) (.var 0))
        (.app (g.rename Nat.succ) (.var 0)) :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.EtaTyping.conversion_iff_pointwise C f g

end Silmaril.Logic.TypeTheory.LambdaPi
