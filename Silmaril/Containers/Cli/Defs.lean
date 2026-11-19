module

public import Silmaril.Containers.Runtime.Defs
public import Silmaril.Cli.Behaviour.Defs
public import Silmaril.Wasi.Cli.Thms

/-! # Experimental CLI satisfaction adapters

Reuse `Cli.Spec.Partial` and WASI's existing `View`/`CliSat`. A view describes every finite
observation, not just successful exits. Nevertheless CLI satisfaction alone still does not
exclude source UB, blocking or divergence. `Certified` requires source noUB independently. -/

@[expose] public section
namespace Silmaril.Containers.Cli

abbrev View := Silmaril.Cli.Input → List Ev → Silmaril.Cli.Seen

/-- One CLI specification, read through a container observation view at every prefix. -/
def Sat {I P : Type} (R : Runtime I P Ev) (image : Silmaril.Cli.Input → I) (view : View)
    (spec : Silmaril.Cli.Spec) : Prop :=
  ∀ i b, R.beh (image i) b → ∀ t, b.Prefix t → spec.Partial i (view i t)

def Certified {I P : Type} (R : Runtime I P Ev) (image : Silmaril.Cli.Input → I) (view : View)
    (spec : Silmaril.Cli.Spec) : Prop :=
  Sat R image view spec ∧ ∀ i, (R.beh (image i)).Sat Spec.noUB

/-- Semantic bridge to actual WASI plays. Its obligations do not mention a desired CLI spec:
all source prefixes must have a play with an admitted host view, at most one invocation,
and the same partial observation. It therefore cannot be discharged by assuming the result. -/
def Realizes {I P : Type} {W : Silmaril.Wasi.World} {St : Type}
    (R : Runtime I P Ev) (image : Silmaril.Cli.Input → I) (view : View)
    (component : W.Model)
    (theory : Silmaril.Cli.Input → Silmaril.Wasm.Resource.Protocol St Silmaril.Wasi.WEv)
    (wasiView : Silmaril.Wasi.Cli.View) : Prop :=
  ∀ i b, R.beh (image i) b → ∀ t, b.Prefix t →
    ∃ play ∈ component, (theory i).Accepts (Silmaril.Wasi.hostView (Silmaril.Wasi.wtrace play)) ∧
      Silmaril.Wasi.Cli.calls wasiView.run (Silmaril.Wasi.wtrace play) ≤ 1 ∧
      view i t = wasiView.seen i (Silmaril.Wasi.wtrace play)

end Silmaril.Containers.Cli
