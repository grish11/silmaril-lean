module

public import Silmaril.Wasm.Logic.Kore.Operational.Conditional.Update.Total.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Binaryen Silmaril.Wasm.SingleThreaded
open GrowWrapper (Forced)
open Silmaril.Logic.Kore.Operational.Conditional.WasmBranch
open Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Native
open Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeAllPath

variable {H : Type} {P : Profile}

/-- The missing infinite-path half of forced-prefix progress, under every host.
This uses local instruction inversion from the dependency, not global determinism. -/
theorem forced_infinite_hit {a b : Core.Config H} (run : Forced (P := P) a b)
    (host : HostSemantics H) (Q : Core.Config H → Prop) (post : Q b) :
    ∀ path : Nat → Core.Config H, path 0 = a →
      (∀ n, Core.Step P host (path n) (path (n+1))) → ∃ n, Q (path n) := by
  induction run with
  | done a =>
    intro path start _
    exact ⟨0, start.symm ▸ post⟩
  | @step a b c active unique tail ih =>
    intro path start edges
    have first : Core.Step P host a (path 1) := start ▸ edges 0
    have forced : path 1 = b := unique _ (hostFree_of_active active host first)
    obtain ⟨n, hit⟩ := ih post (fun i => path (i+1)) forced (fun i => edges (i+1))
    exact ⟨n+1, hit⟩

/-- Every actual infinite or finite maximal path hits the endpoint. The endpoint
need not be terminal and its continuation need not terminate. -/
theorem forced_allEventually {a b : Core.Config H} (run : Forced (P := P) a b)
    (host : HostSemantics H) (Q : Core.Config H → Prop) (post : Q b) :
    Silmaril.Logic.CTL.AllEventually (Core.Step P host) Q a :=
  ⟨forced_infinite_hit run host Q post, forced_allPartial run host Q post⟩

/-- Reaching the target does not assert termination: an actual divergent
continuation extends back through the same forced native prefix. -/
theorem forced_diverges {a b : Core.Config H} (run : Forced (P := P) a b)
    (host : HostSemantics H) (divergence : Core.Diverges P host b) :
    Core.Diverges P host a := by
  induction run with
  | done => exact divergence
  | step active _ _ ih => exact Silmaril.InfiniteTrace.fold (active.of_noHost host) (ih divergence)

/-- Exact CTL AF meaning in the actual native state space and step relation. -/
theorem af_iff_allEventually (P : Profile) (host : HostSemantics H)
    (initial : Core.Config H) (Q : Core.Config H → Prop) :
    Silmaril.Logic.CTL.Sat (predicateModel P host initial Q) eventuallyTarget ↔
      Silmaril.Logic.CTL.AllEventually (Core.Step P host) Q initial :=
  Silmaril.Logic.CTL.Formula.af_iff_all_paths (predicateModel P host initial Q) (.atom ()) initial

/-- The existing CTL→modal μ→pointed fixed-point matching translations preserve
this stronger liveness claim on exactly the actual native state/target model.
This is distinct from the older finite-AllPartial reachability encoding. -/
theorem matching_iff_allEventually (P : Profile) (host : HostSemantics H)
    (initial : Core.Config H) (Q : Core.Config H → Prop) :
    (Silmaril.Logic.Matching.FixedPoint.expandModal
      (Silmaril.Logic.CTL.expandMu (predicateModel P host initial Q))).Satisfies
      (Silmaril.Logic.Matching.FixedPoint.encodeModal eventuallyTarget.toMu) ↔
      Silmaril.Logic.CTL.AllEventually (Core.Step P host) Q initial := by
  rw [Silmaril.Logic.Matching.FixedPoint.expandModal_satisfies]
  have translated := eventuallyTarget.toMu_correct
    (Silmaril.Logic.CTL.expandMu (predicateModel P host initial Q)) initial
  change Silmaril.Logic.ModalMu.Sat
      (Silmaril.Logic.CTL.expandMu (predicateModel P host initial Q)) eventuallyTarget.toMu ↔
    Silmaril.Logic.CTL.Sat
      (Silmaril.Logic.CTL.forgetMu (Silmaril.Logic.CTL.expandMu (predicateModel P host initial Q)))
      eventuallyTarget at translated
  rw [Silmaril.Logic.CTL.forget_expandMu] at translated
  exact translated.trans (af_iff_allEventually P host initial Q)

/-- Initialized compiled entry reaches its actual source/native post-relation
on ALL maximal paths, including infinite paths. The source premises are precisely
those of the earlier finite-complete-path contract. -/
theorem entry_allEventually (L : Layout) (P : Profile) (host : HostSemantics H)
    (s : Store H) (f : Frame) (older : List Val) (tail : List String)
    (rest : List Admin) (valueLocal counterLocal : LocalIdx)
    (q k : BitVec 32) (z n : Int)
    (distinct : valueLocal.toNat ≠ counterLocal.toNat)
    (bound : counterLocal.toNat < f.locals.length)
    (agree : LocalsAgree f valueLocal counterLocal q k)
    (zeroBody : L.zeroBody = BodyDraft.assignBody counterLocal (BitVec.ofInt 32 z))
    (nonzeroBody : L.nonzeroBody = BodyDraft.assignBody counterLocal (BitVec.ofInt 32 n))
    (blockType : f.module.blockType? L.blockType = some ([], []))
    (zlo : -(2^31) ≤ z) (zhi : z < 2^31)
    (nlo : -(2^31) ≤ n) (nhi : n < 2^31) :
    Silmaril.Logic.CTL.AllEventually (Core.Step P host)
      (postRelated L s f older tail rest valueLocal counterLocal q z n
        (afterSource L tail q z n))
      (native L .entry s f older tail rest valueLocal) := by
  have read : f.local? valueLocal = some (some (Val.i32 q)) := by
    have observed := agree.1
    unfold Silmaril.Wasm.Logic.Core.localVal? at observed
    split at observed <;> simp_all
  have run := entry_forced (P := P) L s f older tail rest valueLocal counterLocal q
    (BitVec.ofInt 32 z) (BitVec.ofInt 32 n) read zeroBody nonzeroBody blockType bound
  apply forced_allEventually run host
    (postRelated L s f older tail rest valueLocal counterLocal q z n (afterSource L tail q z n))
  have signed : (BitVec.ofInt 32 (if q = 0 then z else n)).toInt = (if q = 0 then z else n) := by
    split
    · exact signed_representation z zlo zhi
    · exact signed_representation n nlo nhi
  refine ⟨rfl, ?_, write_agrees f valueLocal counterLocal q k _ distinct bound agree, signed⟩
  rw [apply_ite (BitVec.ofInt 32)]

/-- A real loop continuation shows that successful total eventual-hit progress
and actual divergence can coexist. No divergence premise is supplied: the native
loop trace in the unchanged continuation establishes it. -/
theorem entry_eventual_with_loop_divergence (L : Layout) (P : Profile)
    (host : HostSemantics H) (s : Store H) (f : Frame) (tail : List String)
    (rest : List Admin) (valueLocal counterLocal : LocalIdx)
    (q k : BitVec 32) (z n : Int)
    (distinct : valueLocal.toNat ≠ counterLocal.toNat)
    (bound : counterLocal.toNat < f.locals.length)
    (agree : LocalsAgree f valueLocal counterLocal q k)
    (zeroBody : L.zeroBody = BodyDraft.assignBody counterLocal (BitVec.ofInt 32 z))
    (nonzeroBody : L.nonzeroBody = BodyDraft.assignBody counterLocal (BitVec.ofInt 32 n))
    (blockType : f.module.blockType? L.blockType = some ([], []))
    (zlo : -(2^31) ≤ z) (zhi : z < 2^31)
    (nlo : -(2^31) ≤ n) (nhi : n < 2^31)
    (loopContinuation : L.tailCode tail ++ rest =
      [.plain (.loop .empty [.br ⟨⟨0, by decide⟩⟩])]) :
    Silmaril.Logic.CTL.AllEventually (Core.Step P host)
      (postRelated L s f [] tail rest valueLocal counterLocal q z n
        (afterSource L tail q z n)) (native L .entry s f [] tail rest valueLocal) ∧
      Core.Diverges P host (native L .entry s f [] tail rest valueLocal) := by
  refine ⟨entry_allEventually L P host s f [] tail rest valueLocal counterLocal q k z n
    distinct bound agree zeroBody nonzeroBody blockType zlo zhi nlo nhi, ?_⟩
  have read : f.local? valueLocal = some (some (Val.i32 q)) := by
    have observed := agree.1
    unfold Silmaril.Wasm.Logic.Core.localVal? at observed
    split at observed <;> simp_all
  have run := entry_forced (P := P) L s f [] tail rest valueLocal counterLocal q
    (BitVec.ofInt 32 z) (BitVec.ofInt 32 n) read zeroBody nonzeroBody blockType bound
  apply forced_diverges run host
  simpa only [Task.actualDivergence, vals, List.map_nil, List.nil_append, loopContinuation] using
    loop_actualDivergence P host s
      (f.setLocal counterLocal (Val.i32
        (if q = 0 then BitVec.ofInt 32 z else BitVec.ofInt 32 n)))

/-- An actual source update identifies the same after-state in the strong CTL
contract. This theorem uses the source Step, not an unused parser premise. -/
theorem source_entry_af (L : Layout) (P : Profile) (host : HostSemantics H)
    (s : Store H) (f : Frame) (older : List Val) (tail : List String)
    (rest : List Admin) (valueLocal counterLocal : LocalIdx)
    (q k : BitVec 32) (z n : Int)
    (distinct : valueLocal.toNat ≠ counterLocal.toNat)
    (bound : counterLocal.toNat < f.locals.length)
    (agree : LocalsAgree f valueLocal counterLocal q k)
    (zeroBody : L.zeroBody = BodyDraft.assignBody counterLocal (BitVec.ofInt 32 z))
    (nonzeroBody : L.nonzeroBody = BodyDraft.assignBody counterLocal (BitVec.ofInt 32 n))
    (blockType : f.module.blockType? L.blockType = some ([], []))
    (zlo : -(2^31) ≤ z) (zhi : z < 2^31)
    (nlo : -(2^31) ≤ n) (nhi : n < 2^31)
    (d : Config) (sourceStep : Step (rules L z n) (entrySource L tail q k) d) :
    Silmaril.Logic.CTL.Sat
      (predicateModel P host (native L .entry s f older tail rest valueLocal)
        (postRelated L s f older tail rest valueLocal counterLocal q z n d))
      eventuallyTarget := by
  have hd := (source_step_iff L tail q k z n d).mp sourceStep
  subst d
  exact (af_iff_allEventually P host _ _).mpr
    (entry_allEventually L P host s f older tail rest valueLocal counterLocal q k z n
      distinct bound agree zeroBody nonzeroBody blockType zlo zhi nlo nhi)

/-- Transport the actual source-step result all the way to pointed fixed-point
matching, retaining infinite-path eventuality rather than finite AllPartial. -/
theorem source_entry_matching (L : Layout) (P : Profile) (host : HostSemantics H)
    (s : Store H) (f : Frame) (older : List Val) (tail : List String)
    (rest : List Admin) (valueLocal counterLocal : LocalIdx)
    (q k : BitVec 32) (z n : Int)
    (distinct : valueLocal.toNat ≠ counterLocal.toNat)
    (bound : counterLocal.toNat < f.locals.length)
    (agree : LocalsAgree f valueLocal counterLocal q k)
    (zeroBody : L.zeroBody = BodyDraft.assignBody counterLocal (BitVec.ofInt 32 z))
    (nonzeroBody : L.nonzeroBody = BodyDraft.assignBody counterLocal (BitVec.ofInt 32 n))
    (blockType : f.module.blockType? L.blockType = some ([], []))
    (zlo : -(2^31) ≤ z) (zhi : z < 2^31)
    (nlo : -(2^31) ≤ n) (nhi : n < 2^31)
    (d : Config) (sourceStep : Step (rules L z n) (entrySource L tail q k) d) :
    (Silmaril.Logic.Matching.FixedPoint.expandModal
      (Silmaril.Logic.CTL.expandMu
        (predicateModel P host (native L .entry s f older tail rest valueLocal)
          (postRelated L s f older tail rest valueLocal counterLocal q z n d)))).Satisfies
      (Silmaril.Logic.Matching.FixedPoint.encodeModal eventuallyTarget.toMu) := by
  apply (matching_iff_allEventually P host _ _).mpr
  apply (af_iff_allEventually P host _ _).mp
  exact source_entry_af L P host s f older tail rest valueLocal counterLocal q k z n
    distinct bound agree zeroBody nonzeroBody blockType zlo zhi nlo nhi d sourceStep

/-- An actual infinite loop refutes strong AF False, using the native trace
already proved by the dependency rather than recreating a toy cycle. -/
theorem loop_not_allEventually (P : Profile) (host : HostSemantics H)
    (s : Store H) (f : Frame) :
    ¬ Silmaril.Logic.CTL.AllEventually (Core.Step P host) (fun _ => False)
      ⟨s, f, [.plain (.loop .empty [.br ⟨⟨0, by decide⟩⟩])]⟩ := by
  intro total
  obtain ⟨path, start, edges⟩ := loop_actualDivergence P host s f
  obtain ⟨n, impossible⟩ := total.1 path start edges
  exact impossible

/-- Native trapping cannot satisfy an impossible eventual target; finite maximal
paths are still part of strong AF. The existing trap result is reused. -/
theorem unreachable_not_allEventually (P : Profile) (s : Store H) (f : Frame) :
    ¬ Silmaril.Logic.CTL.AllEventually (Core.Step P closedHost) (fun _ => False)
      ⟨s, f, [.plain .unreachable]⟩ := by
  intro total
  exact unreachable_no_false_allPath_matching P s f
    ((compiled_iff_allPartial P closedHost _ _).mpr total.2)

/-- Deadlock without the target is rejected, rather than treated as divergence. -/
theorem stuck_not_allEventually (host : HostSemantics H)
    (w : Core.Config H) (Q : Core.Config H → Prop)
    (stuck : Task.actualStuck P host w) (miss : ¬ Q w) :
    ¬ Silmaril.Logic.CTL.AllEventually (Core.Step P host) Q w :=
  fun total => miss ((Silmaril.Logic.Reachability.allPartial_deadlock _ _ _ stuck).mp total.2)

end Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal
