module

import Silmaril.Machine.SQLite.TrackB.Read.Interaction.Thms

namespace Silmaril.Machine.SQLite.TrackB.Read.Interaction

open Silmaril.Machine.SQLite
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SQLite.TrackA.Read.Interaction (VfsSignature pagerTree pagerHandler vfsTree)

local notation "finiteTrace" => Silmaril.Semantics.TrackA.Interaction.Trace.finite

private def file : FileState := ⟨[], some .readOnly, 0⟩
private def cache : PageRead.Cache := fun slot => if slot = 0 then some .vacant else none
private def page : PageRead.Page := ⟨⟨0⟩, 2, 512⟩
private def buffer : Bytes := readBytes file.bytes 512 512
private def shortOutcome : TrackA.Read.Outcome FileState :=
  ⟨.error (.acquire .shortRead), file, cache, [⟨page.request, .shortRead buffer⟩]⟩

private theorem short_read : run (readOnly 1024) file cache 0 page 41 = shortOutcome := rfl

-- The handled Pager has an ordinary error return, with the short-read exchange in its payload.
example :
    let tree := pagerTree FileState 0 page 41
    let handled := tree.unfold.handle (T := VfsSignature) (pagerHandler (readOnly 1024))
    finiteTrace [] (.returned shortOutcome) ∈ handled.observes (tree.root (), file, cache) := by
  simpa only [short_read] using handledPager_returns_run (readOnly 1024) file cache 0 page 41

-- The lower tree exposes that same short read as a visible dependent exchange.
example :
    let tree := vfsTree cache 0 page 41
    finiteTrace [⟨page.request, ReadReply.shortRead buffer⟩]
      (.returned (.error (.acquire .shortRead), cache)) ∈ tree.unfold.observes (tree.root ()) := by
  have observed := (vfsTree_observes_run (readOnly 1024) file cache 0 page 41).2
  rw [short_read] at observed
  exact observed

#print axioms handledPager_returns_run
#print axioms vfsTree_observes_run
#print axioms handledPager_returns_page
#print axioms readOnly_cold_warm_observations

end Silmaril.Machine.SQLite.TrackB.Read.Interaction
