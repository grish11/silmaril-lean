module

public import Silmaril.Wasm.Logic.Kore.Operational.Conditional.Update.ValueCompiler.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.ValueCompiler
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Logic.Kore.Operational.Conditional.WasmBranch

/-- The selected value-cell rules preserve the independent source counter. -/
theorem step_target (L : Layout) (tail : List String) (q k : BitVec 32)
    (z n : Int) (d : Config)
    (h : Step (rules L z n) (Native.entrySource L tail q k) d) :
    d = afterSource L tail q k z n := by
  obtain ⟨r, hr, v, _hc, hg, he, hd⟩ := (step_iff _ _ _).mp h
  have hr' : r = ⟨L.entry, L.zero, .zero, .val, z⟩ ∨
      r = ⟨L.entry, L.nonzero, .nonzero, .val, n⟩ := by
    simpa only [rules, List.mem_cons, List.not_mem_nil, or_false] using hr
  have hv : q.toInt = v.x := congrArg Config.val he
  have hk : k.toInt = v.counter := congrArg Config.counter he
  have ht : tail = v.tail := (List.cons.inj (congrArg Config.code he)).2
  rcases hr' with rfl | rfl
  · have hz : q = 0 := (signed_zero_iff q).mp (hv.trans (by
      simpa only [Guard.Holds, Guard.eval, intEqual, decide_eq_true_eq] using hg))
    simpa only [afterSource, selected, ite_eq_left hz, Layout.name,
      Rule.afterConfig, ← ht, ← hk] using hd
  · have hz : q ≠ 0 := by
      intro hq
      have hv0 : v.x = 0 := hv.symm.trans ((signed_zero_iff q).mpr hq)
      simp [Guard.Holds, Guard.eval, intEqual, hv0] at hg
    simpa only [afterSource, selected, ite_eq_right hz, Layout.name,
      Rule.afterConfig, ← ht, ← hk] using hd

theorem write_agrees (f : Frame) (valueLocal counterLocal : LocalIdx)
    (q k updated : BitVec 32)
    (distinct : valueLocal.toNat ≠ counterLocal.toNat)
    (bound : valueLocal.toNat < f.locals.length)
    (agree : LocalsAgree f valueLocal counterLocal q k) :
    LocalsAgree (f.setLocal valueLocal (Val.i32 updated))
      valueLocal counterLocal updated k := by
  constructor
  · simp [Silmaril.Wasm.Logic.Core.localVal?, Frame.local?, Frame.setLocal, bound]
  · simpa [Silmaril.Wasm.Logic.Core.localVal?, Frame.local?, Frame.setLocal,
      List.getElem?_set, distinct, Ne.symm distinct] using agree.2

/-- Native prefix inversion and infinite-path progress are reused unchanged.
The assignment target is the guard local itself; the counter local is distinct. -/
theorem raw_step_af {H : Type} {input : String} {p : CheckedProgram}
    (checked : check input = some p) {valueLocal : LocalIdx}
    {tailCode : List String → List Admin} (c : Compiled p valueLocal tailCode)
    (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H)
    (s : Store H) (f : Frame) (older : List Val) (tail : List String)
    (rest : List Admin) (counterLocal : LocalIdx) (q k : BitVec 32)
    (distinct : valueLocal.toNat ≠ counterLocal.toNat)
    (bound : valueLocal.toNat < f.locals.length)
    (agree : LocalsAgree f valueLocal counterLocal q k) (d : Config)
    (raw : Source.RawStep p.declarations (Native.entrySource c.layout tail q k) d) :
    Silmaril.Logic.CTL.Sat
      (NativeTotal.predicateModel P host (native c.layout .entry s f older tail rest valueLocal)
        (postRelated c.layout s f older tail rest valueLocal counterLocal q k
          c.zeroLiteral c.nonzeroLiteral d)) NativeTotal.eventuallyTarget := by
  have sourceStep := (Source.rawStep_iff_step checked _ _).mp raw
  rw [c.installed] at sourceStep
  have hd := step_target c.layout tail q k c.zeroLiteral c.nonzeroLiteral d sourceStep
  have read : f.local? valueLocal = some (some (Val.i32 q)) := by
    have observed := agree.1
    unfold Silmaril.Wasm.Logic.Core.localVal? at observed
    split at observed <;> simp_all
  have run := NativeAllPath.entry_forced (P := P) c.layout s f older tail rest
    valueLocal valueLocal q (BitVec.ofInt 32 c.zeroLiteral) (BitVec.ofInt 32 c.nonzeroLiteral)
    read c.zeroBody c.nonzeroBody (by rw [c.blockType]; rfl) bound
  apply (NativeTotal.af_iff_allEventually P host _ _).mpr
  apply NativeTotal.forced_allEventually run host
  have signed : (BitVec.ofInt 32 (if q = 0 then c.zeroLiteral else c.nonzeroLiteral)).toInt =
      (if q = 0 then c.zeroLiteral else c.nonzeroLiteral) := by
    split
    · exact signed_representation _ c.zeroRange.1 c.zeroRange.2
    · exact signed_representation _ c.nonzeroRange.1 c.nonzeroRange.2
  refine ⟨hd, ?_, write_agrees f valueLocal counterLocal q k _ distinct bound agree, signed⟩
  rw [apply_ite (BitVec.ofInt 32)]

/-- Original text acceptance and exact code selection follow from computation. -/
theorem compileText_sound {input : String} {valueLocal : LocalIdx}
    {tailCode : List String → List Admin}
    {result : (p : CheckedProgram) × Compiled p valueLocal tailCode}
    (compiled : compileText input valueLocal tailCode = some result) :
    check input = some result.1 ∧ compile result.1 valueLocal tailCode = some result.2 := by
  change ((check input).bind fun p => (compile p valueLocal tailCode).bind
    fun c => some (⟨p, c⟩ : (p : CheckedProgram) × Compiled p valueLocal tailCode)) = some result at compiled
  obtain ⟨p, checked, compiled⟩ := Option.bind_eq_some_iff.mp compiled
  obtain ⟨c, hc, same⟩ := Option.bind_eq_some_iff.mp compiled
  cases Option.some.inj same
  exact ⟨checked, hc⟩

/-- End-to-end original-source to strong AF, over actual Core.Step. -/
theorem compileText_raw_af {H : Type} {input : String} {valueLocal : LocalIdx}
    {tailCode : List String → List Admin}
    {result : (p : CheckedProgram) × Compiled p valueLocal tailCode}
    (compiled : compileText input valueLocal tailCode = some result)
    (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H)
    (s : Store H) (f : Frame) (older : List Val) (tail : List String)
    (rest : List Admin) (counterLocal : LocalIdx) (q k : BitVec 32)
    (distinct : valueLocal.toNat ≠ counterLocal.toNat)
    (bound : valueLocal.toNat < f.locals.length)
    (agree : LocalsAgree f valueLocal counterLocal q k) (d : Config)
    (raw : Source.RawStep result.1.declarations
      (Native.entrySource result.2.layout tail q k) d) :
    Silmaril.Logic.CTL.Sat
      (NativeTotal.predicateModel P host
        (native result.2.layout .entry s f older tail rest valueLocal)
        (postRelated result.2.layout s f older tail rest valueLocal counterLocal q k
          result.2.zeroLiteral result.2.nonzeroLiteral d)) NativeTotal.eventuallyTarget :=
  raw_step_af (compileText_sound compiled).1 result.2 P host s f older tail rest
    counterLocal q k distinct bound agree d raw

/-- Matching translation retains the actual native model and strong eventuality. -/
theorem compileText_raw_matching {H : Type} {input : String} {valueLocal : LocalIdx}
    {tailCode : List String → List Admin}
    {result : (p : CheckedProgram) × Compiled p valueLocal tailCode}
    (compiled : compileText input valueLocal tailCode = some result)
    (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H)
    (s : Store H) (f : Frame) (older : List Val) (tail : List String)
    (rest : List Admin) (counterLocal : LocalIdx) (q k : BitVec 32)
    (distinct : valueLocal.toNat ≠ counterLocal.toNat)
    (bound : valueLocal.toNat < f.locals.length)
    (agree : LocalsAgree f valueLocal counterLocal q k) (d : Config)
    (raw : Source.RawStep result.1.declarations
      (Native.entrySource result.2.layout tail q k) d) :
    (Silmaril.Logic.Matching.FixedPoint.expandModal
      (Silmaril.Logic.CTL.expandMu
        (NativeTotal.predicateModel P host
          (native result.2.layout .entry s f older tail rest valueLocal)
          (postRelated result.2.layout s f older tail rest valueLocal counterLocal q k
            result.2.zeroLiteral result.2.nonzeroLiteral d)))).Satisfies
      (Silmaril.Logic.Matching.FixedPoint.encodeModal NativeTotal.eventuallyTarget.toMu) := by
  apply (NativeTotal.matching_iff_allEventually P host _ _).mpr
  apply (NativeTotal.af_iff_allEventually P host _ _).mp
  exact compileText_raw_af compiled P host s f older tail rest counterLocal q k
    distinct bound agree d raw

end Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.ValueCompiler
