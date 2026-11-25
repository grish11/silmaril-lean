module

import Silmaril.Containers.SqliteVfs.NextPage.Thms

namespace Silmaril.Containers.SqliteVfs.NextPage

open Silmaril.Containers
open Silmaril.Containers.SqliteVfs (machine runtime encode)
open Silmaril.Containers.SqliteVfs.Completed (completed)
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.NextPage (fillFollowing)

private def malformed : Handler FileState := fun file request =>
  match request with
  | .read .. => (.ok [], { file with generation := file.generation + 1 })
  | other => readOnly 8 file other

private def file : FileState := ⟨[2, 4], some .readOnly, 0⟩
private def page : Page := ⟨⟨0⟩, 1, 2⟩
private def cache : Cache := fun slot => if slot = 0 ∨ slot = 1 then some .vacant else none

example :
    let trace : Trace := [⟨page.request, .ok []⟩]
    let first := fill malformed file cache 0 page
    first.result = .error .wrongLength ∧
      fillFollowing malformed first 1 (fun _ => some page) = none ∧
      (machine malformed).Exec Mach.seqPolicy (.idle file) (encode trace)
        (.idle { file with generation := 1 }) ∧
      completed (encode trace) = trace := by
  have observed := fill_following_observation malformed file cache 0 page 1 (fun _ => some page)
  exact ⟨rfl, rfl, observed.2.1, observed.2.2.2⟩

#print axioms fill_following_observation

end Silmaril.Containers.SqliteVfs.NextPage
