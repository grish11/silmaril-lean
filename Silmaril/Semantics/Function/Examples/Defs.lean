module

public import Silmaril.Semantics.Function.Semantic.Defs
public import Silmaril.Semantics.Function.Effects.Defs

@[expose] public section
namespace Silmaril.Semantics.Function.Examples

abbrev signature : Signature := ⟨Unit, Unit, Unit, Bool, Unit⟩

def observed : Edge signature := ⟨⟨(), false, .invoke⟩, .direct, .foreign ()⟩

def system : Region.TransitionSystem Bool Bool Unit Unit where
  pc := id
  step source trace dest := source = false ∧ trace = [()] ∧ dest = true
  halt state _ := state = true

def machine : Machine signature where
  State := Bool
  Label := Bool
  Event := Unit
  Stop := Unit
  system _ := system
  owner _ _ state := state = false
  event _ _ _ _ edge := edge = observed
  invocation _ site callee pre post :=
    site = observed.origin ∧ callee = observed.callee ∧ pre = false ∧ post = true
  tailTransfer _ _ _ _ _ := False
  returned _ _ _ _ := False

def boundary : Boundaries machine where
  view _ := ⟨⟨fun _ => ⟨fun source dest => source = false ∧ dest = true⟩⟩,
    fun _ => false, fun _ => {false}, fun _ => {true}⟩
  admit _ _ _ state := state = false
  formed _ _ := True

def candidates : Decomposition signature :=
  fromRegionView (fun _ _ _ entry exits => entry = false ∧ true ∈ exits) boundary.view ()

def report : Analysis signature where
  direct site callee := site = observed.origin ∧ callee = observed.callee
  indirect _ _ := False

def bounded : Analysis signature where
  direct := report.direct
  indirect site bound := site = observed.origin ∧ bound = some {.localFn ()}

def entryEffects : Effects.OnEntry Bool (Set (Sum Unit Unit)) :=
  Effects.forRegion system (· = false) fun event => {event}

def entryBound (state : Bool) : Set (Sum Unit Unit) := if state then ∅ else {.inl ()}

/-- The second bit is a symbolic memory observation chosen by this profile. -/
abbrev Args := Bool × Bool

def argEffects : Effects.OnArgs Args (Set (Sum Unit Unit)) :=
  entryEffects.abstractInput fun args state => state = (args.1 && args.2)

def pairEffects : Effects.OnResult Args Bool (Set Bool) where
  Observation := Bool
  occurs pair read := read = pair.1.2 ∧ pair.2 = (pair.1.1 && read)
  observe read := {read}

end Silmaril.Semantics.Function.Examples
