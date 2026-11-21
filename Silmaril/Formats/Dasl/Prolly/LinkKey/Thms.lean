module

public import Silmaril.Formats.Dasl.Prolly.LinkKey.Defs
public import Silmaril.Formats.Dasl.Prolly.Operations.Thms
public import Silmaril.Formats.Dasl.Prolly.Route.Thms

public section

namespace Silmaril.Formats.Dasl.Prolly.LinkKey

variable {Name : Type}

theorem untag_tagged (link : Link Name) : untag (tagged link) = link := by cases link <;> rfl

theorem tagged_injective : Function.Injective (tagged (Name := Name)) :=
  fun _ _ same => (untag_tagged _).symm.trans ((congrArg untag same).trans (untag_tagged _))

theorem mixed_encodes (link : Link Name) : mixed.encode (tagged link) = .ref link := by cases link <;> rfl

theorem object_before_blob [LinearOrder Name] (left right : Name) :
    tagged (.obj left) < tagged (.blob right) := Sum.Lex.sep _ _

end Silmaril.Formats.Dasl.Prolly.LinkKey
