module

public import Silmaril.Wasi.Component.Accept.Acceptor.Thms
public import Silmaril.Proofs.Wasi.Component.Accept.Acceptor

/-!
# Component acceptor wrappers on the specification components: proofs

The import acceptor only ever calls `accept`. A `reject` import with a different name is
never called, so the strict language is the whole language. Acceptance observes Proponent
moves only (`Strategy.accepted_generate`), and the generating plays call nothing but
`accept`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasi.Component.Accept

open Silmaril.Games Silmaril.Games.Accept Silmaril.Formats.Accept Silmaril.Wasi
  Silmaril.Wasi.Accept

theorem importRejected_importAcceptor (L : ByteLang) (run r : FnName) (hr : r ≠ acceptFn) :
    importRejected (importAcceptor L run) r (args1 bytes?) = ∅ := by
  unfold importRejected
  rw [importAccepted_eq, importAcceptor, Strategy.accepted_generate importObs_not_isO]
  ext w
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨s, ⟨⟨w', -, rfl⟩, -⟩, m, hm, ho⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · simp [importObs, wev] at ho
  · simp only [Function.comp_apply, wev, importObs] at ho
    simp [Ne.symm hr] at ho

end Silmaril.Proofs.Wasi.Component.Accept
