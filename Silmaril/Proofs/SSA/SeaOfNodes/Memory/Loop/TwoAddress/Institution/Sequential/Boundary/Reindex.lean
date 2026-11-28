module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Boundary.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Boundary.Proofs

open RVSDG (Port Tuple)
open Memory.Diamond.Institution (PortMap liftPortMap pullInput pullInput_get)

variable {ambient target next after : List ValueSort} {cells : Nat}

set_option backward.isDefEq.respectTransparency false

theorem map_id (wiring : Wiring ambient next) : wiring.map (fun p => p) = wiring := by
  induction wiring with
  | word _ => rfl
  | forward _ _ ih => simp only [Wiring.map, ih]

theorem map_comp (wiring : Wiring ambient next) (f : PortMap ambient target) (g : PortMap target after) :
    wiring.map (fun p => g (f p)) = (wiring.map f).map g := by
  induction wiring with
  | word _ => rfl
  | forward _ _ ih => simp only [Wiring.map, ih]

private theorem port_map (wiring : Wiring ambient next) (rename : PortMap ambient target)
    {sort : ValueSort} (p : Port next sort) :
    (wiring.map rename).port p = liftPortMap rename (wiring.port p) := by
  induction wiring with
  | word ports => cases p <;> rfl
  | forward port rest ih =>
    cases p with
    | head => rfl
    | tail p => exact ih p

private theorem tuple_ext (left right : Tuple (Val cells) next)
    (same : ∀ {sort}, (p : Port next sort) → left.get p = right.get p) : left = right := by
  induction left with
  | nil => cases right; rfl
  | cons x xs ih =>
    cases right with
    | cons y ys =>
      have head : x = y := same .head
      have tail : xs = ys := ih ys (fun p => same (.tail p))
      rw [head, tail]

theorem select_map (wiring : Wiring ambient next) (rename : PortMap ambient target)
    (word : Word) (input : Tuple (Val cells) target) :
    (wiring.map rename).select word input = wiring.select word (pullInput rename input) := by
  apply tuple_ext
  intro sort p
  simp only [Wiring.select, pullInput_get, port_map]
  cases wiring.port p with
  | head => rfl
  | tail q => exact (pullInput_get rename input q).symm

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Boundary.Proofs
