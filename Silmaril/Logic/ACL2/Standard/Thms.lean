module

public import Silmaril.Logic.ACL2.Standard.Defs

@[expose] public section

namespace Silmaril.Logic.ACL2.Standard

/-- Transfer any core derivation at a realized world to its supplied standard ACL2 interpretation. -/
theorem Realizes.sound {A : Interface} {host : A.HostWorld} {W : World}
    (r : Realizes A host W) (valid : W.Valid) {p : Sentence W.signature}
    (proof : W.Provable p) : p.Holds (A.model host W.signature) :=
  proof.sound _ (valid _ r.definitions)

/-- Transfer a π-institution derivation at a realized world under additional true premises. -/
theorem Realizes.presentation_sound {A : Interface} {host : A.HostWorld} {W : World}
    (r : Realizes A host W) {Γ : Set (Sentence W.signature)} {p : Sentence W.signature}
    (proof : W.presentation.Derives Γ p) (hΓ : ∀ q ∈ Γ, q.Holds (A.model host W.signature)) :
    p.Holds (A.model host W.signature) :=
  proof.sound _ fun q hq => hq.elim (r.definitions q) (hΓ q)

/-- Inclusion preserves old provability and transfers it to a realized ACL2 output world. -/
theorem Realizes.sound_after_include {A : Interface} {host : A.HostWorld} {W V : World}
    (r : Realizes A host V) (b : Book W V) (valid : W.Valid) {p : Sentence W.signature}
    (proof : W.Provable p) : (p.map b.extension.presentation.signature).Holds
      (A.model host V.signature) :=
  r.sound (b.valid valid) (b.provable_include proof)

end Silmaril.Logic.ACL2.Standard
