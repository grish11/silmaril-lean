module

public import Silmaril.Formats.Dasl.Language.Check.Wire.Defs
public import Silmaril.Formats.Dasl.Language.Check.Thms

public section

namespace Silmaril.Formats.Dasl.Wire

theorem queryStore_binding (read : Cid → Option ByteArray) : (queryStore read).Binding :=
  ⟨fun _ _ _ first second => ReadResult.found.inj (Eq.trans (Eq.symm first) second),
    fun _ _ _ first second => ReadResult.found.inj (Eq.trans (Eq.symm first) second)⟩

end Silmaril.Formats.Dasl.Wire
