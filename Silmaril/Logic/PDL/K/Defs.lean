module

public import Silmaril.Logic.PDL.Thms
public import Silmaril.Logic.ModalMu.K.Thms

@[expose] public section
namespace Silmaril.Logic.PDL

/-- Modal K uses only the primitive Unit action; arbitrary PDL programs add expressivity. -/
def encodeK {S : Modal.Signature} : Modal.Formula S → Formula (ModalMu.kSignatures.obj S)
  | .atom a => .atom a
  | .bot => .bot
  | .imp p q => .disj (.neg (encodeK p)) (encodeK q)
  | .box p => .box (.action ()) (encodeK p)

end Silmaril.Logic.PDL
