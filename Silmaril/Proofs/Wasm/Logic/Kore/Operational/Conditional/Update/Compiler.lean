module

public import Silmaril.Wasm.Logic.Kore.Operational.Conditional.Update.Compiler.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Compiler
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Logic.Kore.Operational.Conditional.WasmBranch

/-- Original source interpretation identifies the exact native update target.
Checking is used for raw-AST adequacy; compiled installation is used to select
the emitted branch. Neither a source Step nor installation equality is assumed. -/
theorem raw_step_target {input : String} {p : CheckedProgram}
    (checked : check input = some p) {target : LocalIdx}
    {tailCode : List String → List Admin} (c : Compiled p target tailCode)
    (tail : List String) (q k : BitVec 32) (d : Config)
    (raw : Source.RawStep p.declarations (Native.entrySource c.layout tail q k) d) :
    d = Native.afterSource c.layout tail q c.zeroLiteral c.nonzeroLiteral := by
  apply (Native.source_step_iff c.layout tail q k c.zeroLiteral c.nonzeroLiteral d).mp
  rw [← c.installed]
  exact (Source.rawStep_iff_step checked _ _).mp raw

/-- Every maximal execution of the actual generated code reaches the actual
raw-source successor, including infinite executions with arbitrary continuation.
Only initialized distinct locals and bounds are runtime premises. -/
theorem raw_step_af {H : Type} {input : String} {p : CheckedProgram}
    (checked : check input = some p) {target : LocalIdx}
    {tailCode : List String → List Admin} (c : Compiled p target tailCode)
    (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H)
    (s : Store H) (f : Frame) (older : List Val) (tail : List String)
    (rest : List Admin) (valueLocal : LocalIdx) (q k : BitVec 32)
    (distinct : valueLocal.toNat ≠ target.toNat)
    (bound : target.toNat < f.locals.length)
    (agree : LocalsAgree f valueLocal target q k) (d : Config)
    (raw : Source.RawStep p.declarations (Native.entrySource c.layout tail q k) d) :
    Silmaril.Logic.CTL.Sat
      (NativeTotal.predicateModel P host (native c.layout .entry s f older tail rest valueLocal)
        (Native.postRelated c.layout s f older tail rest valueLocal target q
          c.zeroLiteral c.nonzeroLiteral d)) NativeTotal.eventuallyTarget := by
  have step := (Source.rawStep_iff_step checked _ _).mp raw
  rw [c.installed] at step
  exact NativeTotal.source_entry_af c.layout P host s f older tail rest valueLocal target
    q k c.zeroLiteral c.nonzeroLiteral distinct bound agree c.zeroBody c.nonzeroBody
    (by rw [c.blockType]; rfl) c.zeroRange.1 c.zeroRange.2 c.nonzeroRange.1 c.nonzeroRange.2 d step

/-- The same raw-source transition supplies the pointed matching strong-AF
result on the unchanged native state space and Core.Step relation. -/
theorem raw_step_matching {H : Type} {input : String} {p : CheckedProgram}
    (checked : check input = some p) {target : LocalIdx}
    {tailCode : List String → List Admin} (c : Compiled p target tailCode)
    (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H)
    (s : Store H) (f : Frame) (older : List Val) (tail : List String)
    (rest : List Admin) (valueLocal : LocalIdx) (q k : BitVec 32)
    (distinct : valueLocal.toNat ≠ target.toNat)
    (bound : target.toNat < f.locals.length)
    (agree : LocalsAgree f valueLocal target q k) (d : Config)
    (raw : Source.RawStep p.declarations (Native.entrySource c.layout tail q k) d) :
    (Silmaril.Logic.Matching.FixedPoint.expandModal
      (Silmaril.Logic.CTL.expandMu
        (NativeTotal.predicateModel P host (native c.layout .entry s f older tail rest valueLocal)
          (Native.postRelated c.layout s f older tail rest valueLocal target q
            c.zeroLiteral c.nonzeroLiteral d)))).Satisfies
      (Silmaril.Logic.Matching.FixedPoint.encodeModal NativeTotal.eventuallyTarget.toMu) := by
  apply (NativeTotal.matching_iff_allEventually P host _ _).mpr
  apply (NativeTotal.af_iff_allEventually P host _ _).mp
  exact raw_step_af checked c P host s f older tail rest valueLocal q k distinct bound agree d raw

/-- Successful complete text compilation retains actual parser/checker success
and the actual compiler output, not a separately authored installation witness. -/
theorem compileText_sound {input : String} {target : LocalIdx}
    {tailCode : List String → List Admin}
    {result : (p : CheckedProgram) × Compiled p target tailCode}
    (compiled : compileText input target tailCode = some result) :
    check input = some result.1 ∧ compile result.1 target tailCode = some result.2 := by
  change (check input).bind (fun p => (compile p target tailCode).bind
    (fun c => some (⟨p, c⟩ : (p : CheckedProgram) × Compiled p target tailCode))) = some result at compiled
  obtain ⟨p, checked, compiled⟩ := Option.bind_eq_some_iff.mp compiled
  obtain ⟨c, hc, same⟩ := Option.bind_eq_some_iff.mp compiled
  cases Option.some.inj same
  exact ⟨checked, hc⟩

/-- End-to-end endpoint takes success of the executable text compiler. All
installation, generated-body, state-name and signed-literal facts are internal. -/
theorem compileText_raw_matching {H : Type} {input : String} {target : LocalIdx}
    {tailCode : List String → List Admin}
    {result : (p : CheckedProgram) × Compiled p target tailCode}
    (compiled : compileText input target tailCode = some result)
    (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H)
    (s : Store H) (f : Frame) (older : List Val) (tail : List String)
    (rest : List Admin) (valueLocal : LocalIdx) (q k : BitVec 32)
    (distinct : valueLocal.toNat ≠ target.toNat)
    (bound : target.toNat < f.locals.length)
    (agree : LocalsAgree f valueLocal target q k) (d : Config)
    (raw : Source.RawStep result.1.declarations
      (Native.entrySource result.2.layout tail q k) d) :
    (Silmaril.Logic.Matching.FixedPoint.expandModal
      (Silmaril.Logic.CTL.expandMu
        (NativeTotal.predicateModel P host
          (native result.2.layout .entry s f older tail rest valueLocal)
          (Native.postRelated result.2.layout s f older tail rest valueLocal target q
            result.2.zeroLiteral result.2.nonzeroLiteral d)))).Satisfies
      (Silmaril.Logic.Matching.FixedPoint.encodeModal NativeTotal.eventuallyTarget.toMu) :=
  raw_step_matching (compileText_sound compiled).1 result.2 P host s f older tail rest
    valueLocal q k distinct bound agree d raw

end Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Compiler
