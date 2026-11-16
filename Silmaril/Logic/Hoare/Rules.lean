module

public import Silmaril.Logic.Hoare.Thms

@[expose] public section
namespace Silmaril.Logic.Hoare
variable {L : PDL.Signature} (M : PDL.Model L)

/-- Semantic regular-program judgment, independent of the phased translation. -/
def Valid (p : PDL.Formula L) (a : PDL.Program L) (q : PDL.Formula L) : Prop :=
  ∀ w, p.Holds M w → ∀ v, a.Rel M w v → q.Holds M v

theorem Valid.consequence {p p' q q' : PDL.Formula L} {a : PDL.Program L}
    (h : Valid M p a q) (hpre : ∀ w, p'.Holds M w → p.Holds M w)
    (hpost : ∀ w, q.Holds M w → q'.Holds M w) : Valid M p' a q' :=
  fun w hp v hr => hpost v (h w (hpre w hp) v hr)

theorem Valid.seq {p q r : PDL.Formula L} {a b : PDL.Program L}
    (ha : Valid M p a q) (hb : Valid M q b r) : Valid M p (.seq a b) r := by
  rintro w hp v ⟨u, hau, hbv⟩
  exact hb u (ha w hp u hau) v hbv

theorem Valid.choice {p q : PDL.Formula L} {a b : PDL.Program L}
    (ha : Valid M p a q) (hb : Valid M p b q) : Valid M p (.choice a b) q := by
  intro w hp v hr
  exact hr.elim (ha w hp v) (hb w hp v)

theorem Valid.test (p : PDL.Formula L) : Valid M p (.test p) p := by
  rintro w hp v ⟨he, _⟩
  exact he ▸ hp

/-- Actual finite iteration preserves an invariant, using the existing RTC semantics. -/
theorem Valid.star {p : PDL.Formula L} {a : PDL.Program L}
    (ha : Valid M p a p) : Valid M p (.star a) p := by
  intro w hp v hr
  induction hr with
  | refl => exact hp
  | @tail u v _ huv ih => exact ha u ih v huv

end Silmaril.Logic.Hoare
