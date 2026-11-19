module

public import Silmaril.Containers.Cli.Defs
import Silmaril.Proofs.Containers.Cli.Basic

public section
namespace Silmaril.Containers.Cli

theorem of_wasi {I P St : Type} {W : Silmaril.Wasi.World} {R : Runtime I P Ev}
    {image : Silmaril.Cli.Input → I} {view : View} {component : W.Model}
    {theory : Silmaril.Cli.Input → Silmaril.Wasm.Resource.Protocol St Silmaril.Wasi.WEv}
    {wasiView : Silmaril.Wasi.Cli.View} {spec : Silmaril.Cli.Spec}
    (bridge : Realizes R image view component theory wasiView)
    (sat : Silmaril.Wasi.Cli.CliSat component theory wasiView spec) : Sat R image view spec :=
  Silmaril.Proofs.Containers.Cli.of_wasi bridge sat

end Silmaril.Containers.Cli
