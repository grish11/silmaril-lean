module

public import Silmaril.Logic.Abstraction.FirstOrder.Thms
public import Silmaril.Project.Registry.Institution.Defs

silmaril institution logic.abstraction.inst := Silmaril.Logic.Abstraction.inst
  (title := "Abstraction Logic")

silmaril room logic.abstraction.room := Silmaril.Logic.Abstraction.room
  (title := "Abstraction Logic over a shaped signature")

silmaril institution logic.abstraction.first_order.profile := Silmaril.Logic.Abstraction.FirstOrder.profileInst
  (title := "Abstraction Logic with canonical first-order models")
