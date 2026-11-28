module

public import Silmaril.SSA.Peggy.Bridge.Theta.Defs

public section

namespace Silmaril.SSA.Peggy.Bridge.Theta.Proofs

open CategoryTheory
open PEG.Bridge.Theta.Region (Opcode)
open PEG.Bridge.Theta.Region.Relabel (table mapOps_eq opcode)
open RVSDG (Tuple)

set_option backward.isDefEq.respectTransparency false

variable {Data : Type} {S T U : Signature Data} {carried : List (PEG.Ty Data)}

private theorem code_id (c : Lowered S carried) : mapCode (𝟙 S) c = c := by
  obtain ⟨sigs, ⟨body⟩⟩ := c
  have idOp : (opcode (opMap (𝟙 S)) :
      RVSDG.Institution.OpcodeMap (Opcode S.dialect.ops) (Opcode S.dialect.ops)) = (fun {_ _} op => op) := by
    funext _ _ op
    cases op <;> rfl
  simp only [mapCode, RVSDG.Theta.Institution.relabel, idOp, RVSDG.Institution.mapGraph_id]

private theorem code_comp (f : S ⟶ T) (g : T ⟶ U) (c : Lowered S carried) :
    mapCode (f ≫ g) c = mapCode g (mapCode f c) := by
  obtain ⟨sigs, ⟨body⟩⟩ := c
  have compOp : (opcode (opMap (f ≫ g)) :
      RVSDG.Institution.OpcodeMap (Opcode S.dialect.ops) (Opcode U.dialect.ops)) =
      (fun {_ _} op => opcode (opMap g) (opcode (opMap f) op)) := by
    funext _ _ op
    cases op <;> rfl
  simp only [mapCode, RVSDG.Theta.Institution.relabel, compOp, RVSDG.Institution.mapGraph_comp]

theorem side_id (s : Side S carried) : s.map (𝟙 S) = s := by
  apply Subtype.ext
  exact congrArg₂ (SideData.mk s.val.nodes)
    ((mapOps_eq _ s.val.peg).symm.trans s.val.peg.mapOps_id) (code_id s.val.code)

theorem side_comp (f : S ⟶ T) (g : T ⟶ U) (s : Side S carried) :
    s.map (f ≫ g) = (s.map f).map g := by
  apply Subtype.ext
  refine congrArg₂ (SideData.mk s.val.nodes) ?_ (code_comp f g s.val.code)
  change table (opMap (f ≫ g)) s.val.peg =
    table (opMap g) (table (opMap f) s.val.peg)
  rw [← mapOps_eq, ← mapOps_eq, ← mapOps_eq]
  exact (s.val.peg.mapOps_comp (opMap f) (opMap g)).symm

theorem map_id (e : Equation S) : e.map (𝟙 S) = e := by
  cases e
  simp only [Equation.map, side_id]

theorem map_comp (f : S ⟶ T) (g : T ⟶ U) (e : Equation S) :
    e.map (f ≫ g) = (e.map f).map g := by
  cases e
  simp only [Equation.map, side_comp]

private theorem side_observe (f : S ⟶ T) (s : Side S carried) (m : Model T)
    (entry : Tuple m.val.toPEG.Value carried) (idx : PEG.Index 1) :
    let l := (s.map f).val.peg
    l.observe m.val.toPEG (l.denote m.val.toPEG entry (s.map f).wf) idx =
      s.val.peg.observe (reduct f m).val.toPEG
        (s.val.peg.denote (reduct f m).val.toPEG entry s.wf) idx := by
  have mapped := (s.val.peg.demandWellFounded_mapOps (opMap f)).2 s.wf
  have observed := s.val.peg.observe_denote_mapOps (model := m.val.toPEG) (opMap f) entry s.wf mapped idx
  have transport (a b : PEG.Graph T.dialect.ops carried carried s.val.nodes 1)
      (same : a = b) (ha : WellFounded a.Demand) (hb : WellFounded b.Demand) :
      a.observe m.val.toPEG (a.denote m.val.toPEG entry ha) idx =
        b.observe m.val.toPEG (b.denote m.val.toPEG entry hb) idx := by
    cases same
    rfl
  exact (transport _ _ (mapOps_eq (opMap f) s.val.peg).symm (s.map f).wf mapped).trans observed

theorem holds_map (f : S ⟶ T) (e : Equation S) (m : Model T) :
    (e.map f).Holds m ↔ e.Holds (reduct f m) := by
  unfold Equation.Holds
  simp only [Equation.map]
  constructor <;> intro holds entry idx out
  · simpa only [side_observe] using holds entry idx out
  · simpa only [side_observe] using holds entry idx out

theorem theta_reduct (f : S ⟶ T) (m : Model T) :
    RVSDG.Institution.reduct (opcode (opMap f)) (thetaModel m) = thetaModel (reduct f m) := by
  unfold thetaModel RVSDG.Institution.reduct reduct PEG.Bridge.Theta.Region.model
  congr 1
  funext _ _ op xs
  cases op with
  | primitive => rfl
  | branch =>
    cases xs with | cons flag rest => cases rest; rfl

end Silmaril.SSA.Peggy.Bridge.Theta.Proofs
