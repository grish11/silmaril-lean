module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Institution.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Composition.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Institution.Correctness

/-! Native and generated institutions over typed register permutations. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Institution

open CategoryTheory Silmaril.Logic.Institution
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)
open Tail.Diamond.MLIR.CF.Pruned.Reindex (pull_refl pull_trans)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution
  (Admitted Backend Sentence observationRoom targetRoom)

variable {S T U : Signature} {result : Width}

@[simp] theorem mapAdmitted_id (p : AdmittedAt S result) : mapAdmitted (𝟙 S) p = p :=
  Proofs.mapAdmitted_id p

theorem mapAdmitted_comp (h : S ⟶ T) (k : T ⟶ U) (p : AdmittedAt S result) :
    mapAdmitted (h ≫ k) p = mapAdmitted k (mapAdmitted h p) :=
  Proofs.mapAdmitted_comp h k p

@[simp] theorem reduct_id (input : Valuation S) : reduct (𝟙 S) input = input :=
  pull_refl input

theorem reduct_comp (h : S ⟶ T) (k : T ⟶ U) (input : Valuation U) :
    reduct (h ≫ k) input = reduct h (reduct k input) :=
  (pull_trans h k input).symm

@[simp] theorem Generated.map_id (p : Generated S result) : p.map (𝟙 S) = p :=
  Proofs.generated_id p

/-- Both paths produce equal actual artifacts, including the numbered graph
used to construct the linked Petri net. -/
theorem Generated.map_comp (h : S ⟶ T) (k : T ⟶ U) (p : Generated S result) :
    p.map (h ≫ k) = (p.map h).map k :=
  congrArg Generated.lower (mapAdmitted_comp h k p.source)

/-- Quantification over each actual backend's finite witnesses is independent
on the two sides of the signature change. -/
theorem Generated.returns_map (backend : Backend) (h : S ⟶ T) (p : Generated S result)
    (input : Valuation T) (word : Word result) :
    backend.Returns (p.map h).artifacts input word ↔ backend.Returns p.artifacts (reduct h input) word := by
  rw [p.generated]
  exact @Guarded.backend_returns S.regs T.regs result S.bankEq T.bankEq h backend p.source input word

theorem Generated.observe_map (backend : Backend) (h : S ⟶ T) (p : Generated S result)
    (input : Valuation T) :
    backend.observe (p.map h).artifacts input = backend.observe p.artifacts (reduct h input) :=
  Part.ext fun word => (backend.mem_observe_iff ..).trans
    ((p.returns_map backend h input word).trans (backend.mem_observe_iff ..).symm)

/-- The native partial-word observation, including undefinedness, follows
the same valuation reduct as the generated observers. -/
theorem native_observe_map (h : S ⟶ T) (p : AdmittedAt S result) (input : Valuation T) :
    @Admitted.observe T.regs result T.bankEq (mapAdmitted h p) input =
      @Admitted.observe S.regs result S.bankEq p (reduct h input) :=
  @Guarded.source_observe S.regs T.regs result S.bankEq T.bankEq h p input

/-- The older native corridor supplies the satisfaction condition. -/
noncomputable def nativeCorridor (h : S ⟶ T) : nativeRoom result S ⟶ nativeRoom result T :=
  @Guarded.sourceCorridor S.regs T.regs result S.bankEq T.bankEq h

theorem nativeCorridor_id (S : Signature) : nativeCorridor (result := result) (𝟙 S) = 𝟙 (nativeRoom result S) :=
  Room.hom_ext (Proofs.sentence_id (mapAdmitted (𝟙 S)) mapAdmitted_id)
    (Discrete.functor_ext fun m => congrArg Discrete.mk (reduct_id m))

theorem nativeCorridor_comp (h : S ⟶ T) (k : T ⟶ U) :
    nativeCorridor (result := result) (h ≫ k) = nativeCorridor h ≫ nativeCorridor k :=
  Room.hom_ext (Proofs.sentence_comp (mapAdmitted h) (mapAdmitted k) (mapAdmitted (h ≫ k)) (mapAdmitted_comp h k))
    (Discrete.functor_ext fun m => congrArg Discrete.mk (reduct_comp h k m))

/-- Source-native equations and termination at typed entry valuations. -/
noncomputable def nativeInst (result : Width) : Inst.{0, 0, 0, 0, 0} where
  Sign := Signature
  I := ⟨nativeRoom result, nativeCorridor, nativeCorridor_id, nativeCorridor_comp⟩

theorem generated_satisfaction (backend : Backend) (h : S ⟶ T) (input : Valuation T)
    (sentence : Sentence (Generated S result)) :
    (generatedRoom result backend T).Sat (Discrete.mk input) (sentence.map (Generated.map h)) ↔
      (generatedRoom result backend S).Sat (Discrete.mk (reduct h input)) sentence := by
  cases sentence <;> simp only [generatedRoom, observationRoom, Sentence.map, Sentence.Holds, Generated.observe_map]

noncomputable def generatedCorridor (backend : Backend) (h : S ⟶ T) :
    generatedRoom result backend S ⟶ generatedRoom result backend T :=
  ⟨Sentence.map (Generated.map h), (nativeCorridor (result := result) h).mod,
    fun m s => generated_satisfaction backend h m.as s⟩

theorem generatedCorridor_id (backend : Backend) (S : Signature) :
    generatedCorridor (result := result) backend (𝟙 S) = 𝟙 (generatedRoom result backend S) :=
  Room.hom_ext (Proofs.sentence_id (Generated.map (𝟙 S)) Generated.map_id)
    (Discrete.functor_ext fun m => congrArg Discrete.mk (reduct_id m))

theorem generatedCorridor_comp (backend : Backend) (h : S ⟶ T) (k : T ⟶ U) :
    generatedCorridor (result := result) backend (h ≫ k) =
      generatedCorridor backend h ≫ generatedCorridor backend k :=
  Room.hom_ext (Proofs.sentence_comp (Generated.map h) (Generated.map k) (Generated.map (h ≫ k)) (Generated.map_comp h k))
    (Discrete.functor_ext fun m => congrArg Discrete.mk (reduct_comp h k m))

/-- One generated institution for each of CF, numbered RVSDG and coloured Petri. -/
noncomputable def generatedInst (result : Width) (backend : Backend) : Inst.{0, 0, 0, 0, 0} where
  Sign := Signature
  I := ⟨generatedRoom result backend, generatedCorridor backend, generatedCorridor_id backend,
    generatedCorridor_comp backend⟩

/-- At a fixed boundary the stored graphs can also be read in the existing
#4380 artifact room. The register-change map needs the retained source. -/
noncomputable def artifactsCorridor (backend : Backend) (S : Signature) :
    generatedRoom result backend S ⟶ targetRoom S.regs result backend :=
  ⟨Sentence.map Generated.artifacts, 𝟭 _, fun _ s => by cases s <;> rfl⟩

/-- Emit once at a given signature and keep the same typed model. -/
noncomputable def emitCorridor (backend : Backend) (S : Signature) :
    nativeRoom result S ⟶ generatedRoom result backend S :=
  ⟨Sentence.map Generated.lower, 𝟭 _, fun m s => by
    have sound := @Backend.satisfaction S.regs result S.bankEq backend m.as s
    cases s <;> exact sound⟩

theorem emit_artifacts (backend : Backend) (S : Signature) :
    emitCorridor (result := result) backend S ≫ artifactsCorridor backend S =
      @SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution.comparison S.regs result S.bankEq backend :=
  Room.hom_ext (funext fun sentence => by cases sentence <;> rfl) rfl

theorem emit_natural (backend : Backend) (h : S ⟶ T) :
    nativeCorridor (result := result) h ≫ emitCorridor backend T =
      emitCorridor backend S ≫ generatedCorridor backend h :=
  Room.hom_ext (funext fun sentence => by cases sentence <;> rfl)
    (Discrete.functor_ext fun _ => rfl)

/-- The three compilation comparisons are comorphisms of the local
institutions over the same register-signature category. -/
noncomputable def comparison (result : Width) (backend : Backend) :
    Inst.CoHom (nativeInst result) (generatedInst result backend) where
  Φ := 𝟭 _
  ρ := ⟨emitCorridor backend, fun _ _ h => emit_natural backend h⟩

theorem emit_id (backend : Backend) (S : Signature) :
    nativeCorridor (result := result) (𝟙 S) ≫ emitCorridor backend S = emitCorridor backend S := by
  rw [nativeCorridor_id, Category.id_comp]

/-- Emitting after the composed rename gives exactly the corridor obtained
by emitting first and then translating through each generated room. -/
theorem emit_comp (backend : Backend) (h : S ⟶ T) (k : T ⟶ U) :
    nativeCorridor (result := result) (h ≫ k) ≫ emitCorridor backend U =
      emitCorridor backend S ≫ generatedCorridor backend h ≫ generatedCorridor backend k := by
  rw [emit_natural, generatedCorridor_comp]

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Institution
