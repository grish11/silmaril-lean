module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.RoundTrip.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.LiveOut.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.RegisterRename

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.RegisterRename

open Silmaril.SSA.LambdaRTL.CFG.Cyclic.RoundTrip (renameGraph PacketClosed)

universe v w
variable {V W K : Type w} {F : Type v}

/-- Attach the corresponding live-outs in their original order, at the
same exit labels. The executable renaming and attachment commute. -/
theorem attach_rename [DecidableEq K] (rename : V → W) (fields : K → List V) (g : CFG V K F) :
    LiveOut.attach (fun k => (fields k).map rename) (renameGraph rename g) =
      renameGraph rename (LiveOut.attach fields g) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.RegisterRename.attach_rename rename fields g

/-- An injective register map preserves closure of the labelled rows. -/
theorem closed_rename [DecidableEq V] [DecidableEq W] (rename : V ↪ W)
    (g : CFG V K F) (closed : PacketClosed g) : PacketClosed (renameGraph rename g) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.RegisterRename.closed_rename rename g closed

open Silmaril.Elgot

/-- Compare the projected mutable runs by their common packet-closed lexical
execution. Attachment reads the selected final fields before projection. -/
theorem run_attach_obs_rename {M : Type w → Type w} {α : Type w} [Monad M] [LawfulMonad M]
    [Iterate M] [LawfulElgotMonad M] [DecidableEq V] [DecidableEq W] [DecidableEq K]
    (rename : V ↪ W) (model : Model F M α) (fields : K → List V) (g : CFG V K F)
    (closed : PacketClosed (LiveOut.attach fields g))
    (initial : V → α) (other : W → α) (agrees : ∀ x, other (rename x) = initial x) :
    obs <$> Cyclic.run model (LiveOut.attach (fun k => (fields k).map rename) (renameGraph rename g)) other =
      obs <$> Cyclic.run model (LiveOut.attach fields g) initial := by
  rw [attach_rename]
  exact (RoundTrip.run_rename_obs model _ rename.injective.injOn closed initial other (fun x _ => agrees x)).trans
    (RoundTrip.run_packetClosed_obs model _ closed initial).symm

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.RegisterRename
