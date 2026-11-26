module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution.Correctness

/-! One comparison from admitted source sentences to each actual observer. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution

open CategoryTheory Silmaril.Logic.Institution
open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)

variable {regs : List (ValueSort Width)} {result : Width}

/-- Membership of an exact word uses the backend's own finite witnesses. -/
theorem Backend.mem_observe_iff (backend : Backend) (a : Artifacts regs result)
    (input : Entry regs) (value : Word result) :
    value ∈ backend.observe a input ↔ backend.Returns a input value :=
  Proofs.mem_observe_iff backend a input value

theorem Backend.terminates_iff (backend : Backend) (a : Artifacts regs result) (input : Entry regs) :
    (Sentence.terminates a).Holds (fun p => backend.observe p input) ↔
      ∃ word, backend.Returns a input word := by
  change (backend.observe a input).Dom ↔ _
  exact Part.dom_iff_mem.trans (exists_congr (backend.mem_observe_iff a input))

variable [BankDecidableEq Word (dataPorts regs)]

/-- Replaying the checker on the stored source and facts returns the same admission. -/
theorem Admitted.admit_self (p : Admitted regs result) : admit p.source p.facts = .ok p :=
  Proofs.admit_self p

theorem Admitted.emitted (p : Admitted regs result) :
    Bypass.MLIR.CF.EntryGuard.compile p.source p.facts = .ok p.emit.cf ∧
      Bypass.Numbered.EntryGuard.compile p.source p.facts = .ok p.emit.numbered :=
  Proofs.emitted p

theorem Admitted.mem_observe_iff (p : Admitted regs result) (input : Entry regs) (value : Word result) :
    value ∈ p.observe input ↔ SourceReturns p.source input value :=
  Proofs.mem_observe_source_iff p input value

/-- Exact returned words agree with independent source and target witnesses. -/
theorem Backend.returns_iff_source (backend : Backend) (p : Admitted regs result)
    (input : Entry regs) (value : Word result) :
    backend.Returns p.emit input value ↔ SourceReturns p.source input value :=
  Proofs.returns_iff_source backend p input value

/-- Every generated observer has the same partial result, including undefinedness. -/
theorem Backend.observe_eq_source (backend : Backend) (p : Admitted regs result) (input : Entry regs) :
    backend.observe p.emit input = p.observe input :=
  Part.ext fun value => (backend.mem_observe_iff p.emit input value).trans
    ((backend.returns_iff_source p input value).trans (p.mem_observe_iff input value).symm)

/-- Compare partial equations and finite termination at the same entry valuation. -/
theorem Backend.satisfaction (backend : Backend) (input : Entry regs)
    (sentence : Sentence (Admitted regs result)) :
    (sentence.map Admitted.emit).Holds (fun p => backend.observe p input) ↔
      sentence.Holds (fun p => p.observe input) := by
  cases sentence <;> simp only [Sentence.map, Sentence.Holds, backend.observe_eq_source]

/-- Translate sentences forward and keep the typed valuation as the model reduct. -/
@[expose] noncomputable def comparison (backend : Backend) :
    sourceRoom regs result ⟶ targetRoom regs result backend :=
  ⟨Sentence.map Admitted.emit, 𝟭 _, fun m s => backend.satisfaction m.as s⟩

/-- The fixed-boundary comparison, viewed as a one-signature comorphism. -/
@[expose] noncomputable def oneSignatureComparison (backend : Backend) :
    Inst.CoHom (Syntactic.oneSignature (sourceRoom regs result))
      (Syntactic.oneSignature (targetRoom regs result backend)) :=
  Syntactic.oneSignatureMap (comparison backend)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution
