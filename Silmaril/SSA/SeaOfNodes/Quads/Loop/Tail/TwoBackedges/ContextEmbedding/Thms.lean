module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Rooms.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Transport
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Observation
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Corridors

/-! Local composition laws and correctness of checker replay and actual emission. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding

open CategoryTheory Silmaril.Logic.Institution
open SeaOfNodes.Diamond (ValueSort dataPorts sortValue)
open SeaOfNodes.Diamond.SCCP (TupleCovers)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Port)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted Backend Sentence)
open Reindex.Guarded.Institution (AdmittedAt Generated Valuation nativeRoom generatedRoom emitCorridor)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {S T U V : EntrySignature} {result : Width}

/-- The fresh value is placed at the requested zero-based position. -/
theorem insertionOrder_fresh (fresh : ValueSort Width) (regs : List (ValueSort Width))
    (pos : Fin (regs.length + 1)) :
    slot ((insertionOrder fresh regs pos) (.value fresh) .head) = pos.val :=
  Proofs.insertionOrder_fresh fresh regs pos

theorem reduct_insertValue (S : EntrySignature) (fresh : ValueSort Width) (pos : Fin (S.regs.length + 1))
    (value : sortValue Word fresh) (input : Valuation S) :
    (insert S fresh pos).reduct (insertValue fresh pos value input) = input :=
  Proofs.reduct_insertValue S fresh pos value input

namespace Embedding

@[simp] theorem id_trans (path : Embedding S T) : (Embedding.id S).trans path = path := rfl

@[simp] theorem trans_id (path : Embedding S T) : path.trans (.id T) = path :=
  Proofs.trans_id path

theorem trans_assoc (first : Embedding S T) (second : Embedding T U) (third : Embedding U V) :
    (first.trans second).trans third = first.trans (second.trans third) :=
  Proofs.trans_assoc first second third

theorem portMap_injective (path : Embedding S T) (t : SeaOfNodes.Diamond.Ty Width) :
    Function.Injective (path.portMap t) :=
  Proofs.portMap_injective path t

theorem portMap_trans (first : Embedding S T) (second : Embedding T U) {t : SeaOfNodes.Diamond.Ty Width}
    (port : Port (dataPorts S.regs) t) :
    (first.trans second).portMap t port = second.portMap t (first.portMap t port) :=
  Proofs.portMap_trans first second port

@[simp] theorem reduct_id (input : Valuation S) : (Embedding.id S).reduct input = input := rfl

theorem reduct_trans (first : Embedding S T) (second : Embedding T U) (input : Valuation U) :
    (first.trans second).reduct input = first.reduct (second.reduct input) :=
  Proofs.reduct_trans first second input

theorem reduct_get (path : Embedding S T) (input : Valuation T) {t : SeaOfNodes.Diamond.Ty Width}
    (port : Port (dataPorts S.regs) t) :
    (path.reduct input).get port = input.get (path.portMap t port) :=
  Proofs.reduct_get path input port

theorem reduct_congr (first second : Embedding S T)
    (agrees : ∀ t p, first.portMap t p = second.portMap t p) (input : Valuation T) :
    first.reduct input = second.reduct input :=
  Proofs.reduct_congr first second agrees input

theorem mapGenerated_lower (path : Embedding S T) (p : AdmittedAt S result) :
    path.mapGenerated (Generated.lower p) = Generated.lower (path.mapAdmitted p) :=
  Proofs.mapGenerated_lower path p

theorem selectedSide_map (path : Embedding S T) (p : AdmittedAt S result) :
    selectedSide (path.mapAdmitted p) = selectedSide p :=
  Proofs.selectedSide_map path p

theorem coverage_iff (path : Embedding S T) (p : AdmittedAt S result) (input : Valuation T) :
    TupleCovers (@Admitted.facts _ _ T.bankEq (path.mapAdmitted p)) input ↔
      TupleCovers (@Admitted.facts _ _ S.bankEq p) (path.reduct input) :=
  Proofs.coverage_iff path p input

theorem replay_eq (path : Embedding S T) (p : AdmittedAt S result) :
    path.replay p = .ok (path.mapAdmitted p) :=
  @Admitted.admit_self _ _ T.bankEq (path.mapAdmitted p)

theorem compile_eq (path : Embedding S T) (p : AdmittedAt S result) :
    path.compile p = .ok (path.mapGenerated (Generated.lower p)) := by
  rw [mapGenerated_lower]
  exact congrArg (Except.map Generated.lower) (path.replay_eq p)

theorem native_observe (path : Embedding S T) (p : AdmittedAt S result) (input : Valuation T) :
    @Admitted.observe _ _ T.bankEq (path.mapAdmitted p) input =
      @Admitted.observe _ _ S.bankEq p (path.reduct input) :=
  Proofs.native_observe path p input

theorem backend_returns (path : Embedding S T) (backend : Backend) (p : Generated S result)
    (input : Valuation T) (word : Word result) :
    backend.Returns (path.mapGenerated p).artifacts input word ↔
      backend.Returns p.artifacts (path.reduct input) word :=
  Proofs.backend_returns path backend p input word

/-- Both actual artifacts have their own finite witness. -/
theorem compile_returns_iff (path : Embedding S T) (backend : Backend) (p : AdmittedAt S result)
    {target : Generated T result} (success : path.compile p = .ok target) (input : Valuation T) (word : Word result) :
    backend.Returns target.artifacts input word ↔
      backend.Returns (Generated.lower p).artifacts (path.reduct input) word := by
  cases Except.ok.inj ((path.compile_eq p).symm.trans success)
  exact path.backend_returns backend (Generated.lower p) input word

theorem compile_noReturn_iff (path : Embedding S T) (backend : Backend) (p : AdmittedAt S result)
    {target : Generated T result} (success : path.compile p = .ok target) (input : Valuation T) :
    (¬ ∃ word, backend.Returns target.artifacts input word) ↔
      ¬ ∃ word, backend.Returns (Generated.lower p).artifacts (path.reduct input) word :=
  not_congr (exists_congr (path.compile_returns_iff backend p success input))

theorem compile_observe (path : Embedding S T) (backend : Backend) (p : AdmittedAt S result)
    {target : Generated T result} (success : path.compile p = .ok target) (input : Valuation T) :
    backend.observe target.artifacts input = backend.observe (Generated.lower p).artifacts (path.reduct input) :=
  Part.ext fun value => (backend.mem_observe_iff ..).trans
    ((path.compile_returns_iff backend p success input value).trans (backend.mem_observe_iff ..).symm)

/-- Different factorizations of the same typed port embedding give the same partial word. -/
theorem compile_congr (first second : Embedding S T)
    (agrees : ∀ t p, first.portMap t p = second.portMap t p)
    (backend : Backend) (p : AdmittedAt S result) {left right : Generated T result}
    (leftOk : first.compile p = .ok left) (rightOk : second.compile p = .ok right) (input : Valuation T) :
    backend.observe left.artifacts input = backend.observe right.artifacts input :=
  (first.compile_observe backend p leftOk input).trans
    ((congrArg (backend.observe (Generated.lower p).artifacts) (first.reduct_congr second agrees input)).trans
     (second.compile_observe backend p rightOk input).symm)

/-- Staged checker replay and one replay after composition have the same observation. -/
theorem compile_staged (first : Embedding S T) (second : Embedding T U)
    (backend : Backend) (p : AdmittedAt S result) {middle : Generated T result} {staged direct : Generated U result}
    (middleOk : first.compile p = .ok middle) (stagedOk : second.compile middle.source = .ok staged)
    (directOk : (first.trans second).compile p = .ok direct) (input : Valuation U) :
    backend.observe staged.artifacts input = backend.observe direct.artifacts input := by
  refine (second.compile_observe backend middle.source stagedOk input).trans ?_
  refine (congrArg (fun a => backend.observe a (second.reduct input)) middle.generated.symm).trans ?_
  rw [first.compile_observe backend p middleOk, ← reduct_trans, ← (first.trans second).compile_observe backend p directOk]

@[simp] theorem nativeCorridor_id (S : EntrySignature) :
    (Embedding.id S).nativeCorridor (result := result) = 𝟙 (nativeRoom result S) := rfl

theorem nativeCorridor_trans (first : Embedding S T) (second : Embedding T U) :
    (first.trans second).nativeCorridor (result := result) = first.nativeCorridor ≫ second.nativeCorridor := by
  induction first <;> simp only [trans, nativeCorridor, Category.id_comp, Category.assoc, *]

@[simp] theorem generatedCorridor_id (backend : Backend) (S : EntrySignature) :
    (Embedding.id S).generatedCorridor (result := result) backend = 𝟙 (generatedRoom result backend S) := rfl

theorem generatedCorridor_trans (backend : Backend) (first : Embedding S T) (second : Embedding T U) :
    (first.trans second).generatedCorridor (result := result) backend =
      first.generatedCorridor backend ≫ second.generatedCorridor backend := by
  induction first <;> simp only [trans, generatedCorridor, Category.id_comp, Category.assoc, *]

theorem native_sen (path : Embedding S T) (sentence : Sentence (AdmittedAt S result)) :
    path.nativeCorridor.sen sentence = sentence.map path.mapAdmitted :=
  Proofs.native_sen path sentence

theorem generated_sen (path : Embedding S T) (backend : Backend) (sentence : Sentence (Generated S result)) :
    (path.generatedCorridor backend).sen sentence = sentence.map path.mapGenerated :=
  Proofs.generated_sen path backend sentence

theorem native_mod (path : Embedding S T) (input : Valuation T) :
    (path.nativeCorridor (result := result)).mod.obj (Discrete.mk input) = Discrete.mk (path.reduct input) :=
  Proofs.native_mod path input

theorem generated_mod (path : Embedding S T) (backend : Backend) :
    (path.generatedCorridor (result := result) backend).mod = (path.nativeCorridor (result := result)).mod :=
  Proofs.generated_mod path backend

/-- Translate partial equations and termination at the reduced valuation. -/
theorem native_satisfaction (path : Embedding S T) (input : Valuation T) (sentence : Sentence (AdmittedAt S result)) :
    (nativeRoom result T).Sat (Discrete.mk input) (sentence.map path.mapAdmitted) ↔
      (nativeRoom result S).Sat (Discrete.mk (path.reduct input)) sentence := by
  simpa only [native_sen, native_mod] using path.nativeCorridor.sat (Discrete.mk input) sentence

theorem generated_satisfaction (path : Embedding S T) (backend : Backend) (input : Valuation T)
    (sentence : Sentence (Generated S result)) :
    (generatedRoom result backend T).Sat (Discrete.mk input) (sentence.map path.mapGenerated) ↔
      (generatedRoom result backend S).Sat (Discrete.mk (path.reduct input)) sentence := by
  simpa only [generated_sen, generated_mod, native_mod] using
    (path.generatedCorridor backend).sat (Discrete.mk input) sentence

/-- The existing emission comparison commutes with the composed local corridors. -/
theorem emit_commutes (path : Embedding S T) (backend : Backend) :
    path.nativeCorridor (result := result) ≫ emitCorridor backend T =
      emitCorridor backend S ≫ path.generatedCorridor backend :=
  Proofs.emit_commutes path backend

end Embedding

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding
