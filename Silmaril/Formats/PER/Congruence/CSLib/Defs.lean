module

public import Cslib.Foundations.Syntax.Congruence
public import Silmaril.Formats.PER.Congruence.Defs

@[expose] public section

namespace Silmaril.Formats.PER.Constructors

variable {α : Type}

/-- A single-hole constructor frame that is enabled for every supported filler.
All other children are fixed and supported. This restriction makes filling total
on the support subtype, as required by CSLib. -/
structure SupportFrame (C : Constructors α) (R : PER α) where
  shape : C.Shape
  hole : C.Pos shape
  args : {x // R.Dom x} → C.Pos shape → {x // R.Dom x}
  atHole : ∀ filler, args filler hole = filler
  fixed : ∀ left right pos, pos ≠ hole → args left pos = args right pos
  enabled : ∀ filler, C.enabled shape (fun pos => (args filler pos).val)

def SupportFrame.fill {C : Constructors α} {R : PER α} (closed : C.Closed R) (frame : C.SupportFrame R)
    (filler : {x // R.Dom x}) : {x // R.Dom x} :=
  ⟨C.make frame.shape (fun pos => (frame.args filler pos).val),
    closed frame.shape (frame.enabled filler) (frame.enabled filler) (fun pos => (frame.args filler pos).property)⟩

/-- Interpret these frames as CSLib contexts without installing a global instance. -/
@[instance_reducible]
def supportContexts (C : Constructors α) (R : PER α) (closed : C.Closed R) : Cslib.HasContext {x // R.Dom x} where
  Context := C.SupportFrame R
  fill := SupportFrame.fill closed

end Silmaril.Formats.PER.Constructors
