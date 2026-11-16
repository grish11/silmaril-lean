module

public import Silmaril.Proofs.Logic.Temporal.CTLStar.Renaming

@[expose] public section
namespace Silmaril.Logic.Temporal.CTLStar
open CategoryTheory

/-- An actual pointed, valuation-preserving frame isomorphism. -/
structure FrameIso {S : Signature} (M N : Model S) where
  equiv : M.toModal.World ≃ N.toModal.World
  point : equiv M.toModal.point = N.toModal.point
  atoms : ∀ a w, M.toModal.valuation a w ↔ N.toModal.valuation a (equiv w)
  edges : ∀ w v, M.toModal.accessible w v ↔ N.toModal.accessible (equiv w) (equiv v)

def FrameIso.symm {S : Signature} {M N : Model S} (e : FrameIso M N) : FrameIso N M where
  equiv := e.equiv.symm
  point := by rw [← e.point]; exact e.equiv.symm_apply_apply _
  atoms a w := by simpa only [Equiv.apply_symm_apply] using (e.atoms a (e.equiv.symm w)).symm
  edges w v := by simpa only [Equiv.apply_symm_apply] using
    (e.edges (e.equiv.symm w) (e.equiv.symm v)).symm

/-- Reindex actual maximal paths, preserving their finite/infinite extent exactly. -/
def FrameIso.mapPath {S : Signature} {M N : Model S} (e : FrameIso M N)
    (p : Path M.toModal.accessible) : Path N.toModal.accessible where
  state i := e.equiv (p.state i)
  last := p.last
  edges i hi := (e.edges _ _).mp (p.edges i hi)
  terminal n hn v hv := by
    obtain ⟨u, rfl⟩ := e.equiv.surjective v
    exact p.terminal n hn u ((e.edges _ _).mpr hv)

def FrameIso.toModalHom {S : Signature} {M N : Model S} (e : FrameIso M N) :
    M.toModal ⟶ N.toModal where
  map := e.equiv
  point := e.point
  atoms := e.atoms
  forth w v h := (e.edges w v).mp h
  back w v h := ⟨e.equiv.symm v,
    (e.edges w (e.equiv.symm v)).mpr (by simpa only [Equiv.apply_symm_apply] using h),
    e.equiv.apply_symm_apply v⟩

theorem modalHom_ext {S : Signature} {M N : Modal.Model S}
    {f g : M ⟶ N} (h : f.map = g.map) : f = g := by
  cases f
  cases g
  cases h
  rfl

def FrameIso.toModalIso {S : Signature} {M N : Model S} (e : FrameIso M N) :
    M.toModal ≅ N.toModal where
  hom := e.toModalHom
  inv := e.symm.toModalHom
  hom_inv_id := modalHom_ext (funext fun w => e.equiv.symm_apply_apply w)
  inv_hom_id := modalHom_ext (funext fun w => e.equiv.apply_symm_apply w)

mutual
theorem StateFormula.holds_iso {S : Signature} {M N : Model S} (e : FrameIso M N)
    (p : StateFormula S) (w : M.toModal.World) :
    p.Holds M w ↔ p.Holds N (e.equiv w) := by
  cases p with
  | atom a => exact e.atoms a w
  | bot => rfl
  | neg p => exact not_congr (p.holds_iso e w)
  | conj p q => exact and_congr (p.holds_iso e w) (q.holds_iso e w)
  | existsPath p =>
    constructor
    · rintro ⟨path, h0, hp⟩
      refine ⟨e.mapPath path, congrArg e.equiv h0, ?_⟩
      exact (p.holds_iso e path (e.mapPath path) rfl (fun _ => rfl) 0).mp hp
    · rintro ⟨path, h0, hp⟩
      let pre := e.symm.mapPath path
      have hstates (i : Nat) : e.equiv (pre.state i) = path.state i :=
        e.equiv.apply_symm_apply _
      refine ⟨pre, e.equiv.injective ((hstates 0).trans h0), ?_⟩
      exact (p.holds_iso e pre path rfl hstates 0).mpr hp

theorem PathFormula.holds_iso {S : Signature} {M N : Model S} (e : FrameIso M N)
    (p : PathFormula S) (path : Path M.toModal.accessible) (other : Path N.toModal.accessible)
    (hlast : path.last = other.last) (hstates : ∀ i, e.equiv (path.state i) = other.state i)
    (i : Nat) : p.Holds M path i ↔ p.Holds N other i := by
  cases p with
  | state p =>
    change p.Holds M (path.state i) ↔ p.Holds N (other.state i)
    rw [← hstates i]
    exact p.holds_iso e _
  | neg p => exact not_congr (p.holds_iso e path other hlast hstates i)
  | conj p q =>
    exact and_congr (p.holds_iso e path other hlast hstates i)
      (q.holds_iso e path other hlast hstates i)
  | next p =>
    exact and_congr (by unfold Path.Valid; rw [hlast])
      (p.holds_iso e path other hlast hstates (i+1))
  | «until» p q =>
    exact exists_congr fun d => and_congr (by unfold Path.Valid; rw [hlast])
      (and_congr (q.holds_iso e path other hlast hstates (i+d))
        (forall_congr' fun j => imp_congr_right fun _ =>
          p.holds_iso e path other hlast hstates (i+j)))
end

/-- Every actual categorical Kripke isomorphism supplies this semantic transport API. -/
def FrameIso.ofModalIso {S : Signature} {M N : Model S} (e : M.toModal ≅ N.toModal) :
    FrameIso M N := by
  let equiv : M.toModal.World ≃ N.toModal.World :=
    { toFun := e.hom.map
      invFun := e.inv.map
      left_inv := fun w => congrArg (fun f : M.toModal ⟶ M.toModal => f.map w) e.hom_inv_id
      right_inv := fun w => congrArg (fun f : N.toModal ⟶ N.toModal => f.map w) e.inv_hom_id }
  refine ⟨equiv, e.hom.point, e.hom.atoms, ?_⟩
  intro w v
  constructor
  · exact e.hom.forth w v
  · intro h
    have hi := e.inv.forth _ _ h
    change M.toModal.accessible (equiv.symm (equiv w)) (equiv.symm (equiv v)) at hi
    simpa only [Equiv.symm_apply_apply] using hi

theorem StateFormula.sat_iso {S : Signature} {M N : Model S} (e : FrameIso M N)
    (p : StateFormula S) : Sat M p ↔ Sat N p := by
  unfold Sat
  rw [← e.point]
  exact p.holds_iso e M.toModal.point

end Silmaril.Logic.Temporal.CTLStar
