module

public import Silmaril.Games.BrookesSC.Thms

@[expose] public section

namespace Silmaril.Games.BrookesSC.Examples

open CategoryTheory Silmaril.Logic.BrookesSC

abbrev world : World := ⟨Unit, Bool, fun _ => Bool, Unit, Empty, Empty.elim⟩
def interface : Signature world := ⟨fun _ => Unit⟩

def redirect : Designation world → Designation world
  | .primitive (.load t m _) => .primitive (.load t m true)
  | d => d

def redirectReply (d : Designation world) : (redirect d).Reply → d.Reply :=
  match d with
  | .primitive (.load ..) => id
  | .primitive (.store ..) => id
  | .primitive (.acquire ..) => id
  | .primitive (.release ..) => id
  | .external _ => id

/-- At the plain effect interface it is well typed to send every load to the
same cell and keep the Boolean reply. -/
def aliasReads : Sig.Hom (events interface) (events interface) :=
  ⟨fun q => ⟨redirect q.1, ()⟩, fun q => redirectReply q.1⟩

/-- Such aliasing cannot arise from an SC arrow in the fixed world. -/
theorem aliasReads_not_liftable : ¬ ∃ f : interface ⟶ interface, eventHom f = aliasReads := by
  rintro ⟨f, eq⟩
  let q : (events interface).Op := ⟨.primitive (.load () .plain false), ()⟩
  have impossible := congrArg (fun h : Sig.Hom (events interface) (events interface) => (h.op q).1) eq
  cases impossible

end Silmaril.Games.BrookesSC.Examples
