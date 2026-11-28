module

import Silmaril.Wasm.Institution.Operational.Loops.Indexed.Thms
import Silmaril.Wasm.V1.ToCore.Types

namespace Silmaril.Wasm.Institution.Operational.Loops.IndexedHostExamples

open Execution.Runtime (Frame FuncAddr MemAddr MemInst ModuleInst Value)
open Wasm.Lime1.Execution

private abbrev i32 := Value.int .i32
private abbrev i64 := Value.int .i64
private def slot : MemAddr := ⟨0⟩
private def rootAddress : FuncAddr := ⟨0⟩
private def producerAddress : FuncAddr := ⟨1⟩
private def laterAddress : FuncAddr := ⟨2⟩
private def signature : Wasm.Lime1.FuncType := ⟨[.int .i64], [.int .i32]⟩
private def producerType : Wasm.Lime1.FuncType := ⟨[.int .i64], [.int .i32, .int .i64, .int .i32]⟩
private def laterType : Wasm.Lime1.FuncType := ⟨[.int .i64, .int .i32], [.int .i32]⟩

private def loop : LimeIndexedLoop := ⟨⟨0⟩, signature, [.call ⟨0⟩, .brIf ⟨0⟩, .drop]⟩
private def root : Wasm.Lime1.Func :=
  ⟨⟨0⟩, [], [.intConst .i64 42, .localGet ⟨0⟩, loop.instr, .call ⟨1⟩]⟩
private def mod : ModuleInst :=
  { types := [signature], funcs := [producerAddress, laterAddress], memories := [slot] }
private def saved : List Value := [i64 42]
private def original : List Value := [i64 7]
private def updated : List Value := [i64 12]
private def returned : List Value := [i32 23]
private def active : Frame := ⟨original, mod⟩
private def caller : Frame := ⟨[i32 99], { funcs := [rootAddress] }⟩
private def tail : List Admin := [.source (.call ⟨1⟩)]
private def afterProducer : List Admin := [.source (.brIf ⟨0⟩), .source .drop]

private def mem (marker : UInt8) : MemInst := ⟨⟨#[0xaa, marker, 0xbb]⟩, none⟩
private def store (marker : UInt8) : Store Nat :=
  { funcs := [.wasm signature mod root, .host producerType 10, .host laterType 11],
    memories := [mem marker] }

private def host : HostSemantics Nat := fun id s operands outcome =>
  (id = 10 ∧ s = store 0 ∧ operands = original ∧
    outcome = .returned (store 1) (.values ([i32 75] ++ updated ++ [i32 1]))) ∨
  (id = 10 ∧ s = store 1 ∧ operands = updated ∧
    outcome = .returned (store 2) (.values (returned ++ [i64 88, i32 0]))) ∨
  (id = 11 ∧ s = store 2 ∧ operands = saved ++ returned ∧
    outcome = .returned s (.values [i32 5]))

private def function (cfg : Config Nat) : Config Nat :=
  ⟨cfg.store, caller, [.frame 1 cfg.frame [.label 1 [] cfg.code]]⟩

private theorem inFunction {s s' : Store Nat} {a b : List Admin}
    (step : Step host ⟨s, active, a⟩ ⟨s', active, b⟩) :
    Step host (function ⟨s, active, a⟩) (function ⟨s', active, b⟩) :=
  .frame (.label step 1 []) 1 caller

private def iteration (s : Store Nat) (code : List Admin) : Config Nat :=
  function ⟨s, active, values saved ++ .label 1 [loop.instr] code :: tail⟩

private theorem inIteration {s s' : Store Nat} {a b : List Admin}
    (step : Step host ⟨s, active, a⟩ ⟨s', active, b⟩) :
    Step host (iteration s a) (iteration s' b) :=
  inFunction (.context (.label step 1 [loop.instr]) saved tail)

private def launch : Config Nat := ⟨store 0, caller, values original ++ [.source (.call ⟨0⟩)]⟩

private theorem initialEntry :
    Steps host launch (iteration (store 0) (values original ++ expression loop.body)) := by
  have resolved : Step host launch ⟨store 0, caller, values original ++ [.invoke rootAddress]⟩ :=
    .context (.call _ _ ⟨0⟩ rootAddress rfl) original []
  have enters : Step host ⟨store 0, caller, values original ++ [.invoke rootAddress]⟩
      (function ⟨store 0, active, expression root.body⟩) :=
    .invokeWasm _ _ rootAddress signature mod root original rfl rfl
  have reads : Step host (function ⟨store 0, active, expression root.body⟩)
      (function ⟨store 0, active, values (saved ++ original) ++ .source loop.instr :: tail⟩) :=
    inFunction (.context (.localGet _ _ ⟨0⟩ (i64 7) rfl) saved (.source loop.instr :: tail))
  have opens := (loop.entry_iff (host := host) (s := store 0) (saved := saved) (rest := tail)
    (args := original) (f := active) rfl rfl).mpr rfl
  exact ((Relation.ReflTransGen.single resolved).tail enters |>.tail reads).tail (inFunction opens)

private theorem resolvesProducer (s : Store Nat) (args : List Value) :
    Step host (iteration s (values args ++ .source (.call ⟨0⟩) :: afterProducer))
      (iteration s (values args ++ .invoke producerAddress :: afterProducer)) :=
  inIteration (by
    simpa only [List.singleton_append, List.append_assoc] using
      (Step.context (host := host) (.call s active ⟨0⟩ producerAddress rfl) args afterProducer))

private theorem firstReturn :
    Steps host launch (iteration (store 1) (values ([i32 75] ++ updated ++ [i32 1]) ++ afterProducer)) := by
  have outcome : host 10 (store 0) original (.returned (store 1) (.values ([i32 75] ++ updated ++ [i32 1]))) :=
    .inl ⟨rfl, rfl, rfl, rfl⟩
  have returns := inIteration (.context (.invokeHost _ _ _ producerAddress producerType 10 original _ rfl rfl outcome)
    [] afterProducer)
  exact (initialEntry.tail (resolvesProducer (store 0) original)).tail returns

private theorem reentry :
    Steps host launch (iteration (store 1) (values updated ++ expression loop.body)) := by
  have taken : Step host (iteration (store 1) (values ([i32 75] ++ updated ++ [i32 1]) ++ afterProducer))
      (iteration (store 1) (values ([i32 75] ++ updated) ++ [.source (.br ⟨0⟩), .source .drop])) :=
    inIteration (.context (.pure _ _ (.brIfNonzero ⟨0⟩ 1 (by decide))) ([i32 75] ++ updated) [.source .drop])
  have exit := (loop.restart_iff (host := host) (s := store 1) (f := active) (saved := saved) (rest := tail)
    (scratch := [i32 75]) (args := updated) (skipped := [.source .drop]) rfl rfl).mpr rfl
  have opens := (loop.entry_iff (host := host) (s := store 1) (saved := saved) (rest := tail)
    (args := updated) (f := active) rfl rfl).mpr rfl
  exact ((firstReturn.tail taken).tail (inFunction exit)).tail (inFunction opens)

-- The next invocation sees the i64 produced by the first host and that
-- host's returned store. The original parameter still belongs to the frame.
example : Steps host launch (iteration (store 1) (values updated ++ .invoke producerAddress :: afterProducer)) :=
  reentry.tail (resolvesProducer (store 1) updated)

private theorem reachesLater :
    Steps host launch (function ⟨store 2, active, values (saved ++ returned) ++ [.invoke laterAddress]⟩) := by
  have outcome : host 10 (store 1) updated (.returned (store 2) (.values (returned ++ [i64 88, i32 0]))) :=
    .inr (.inl ⟨rfl, rfl, rfl, rfl⟩)
  have returns : Step host (iteration (store 1) (values updated ++ .invoke producerAddress :: afterProducer))
      (iteration (store 2) (values (returned ++ [i64 88, i32 0]) ++ afterProducer)) :=
    inIteration (.context (.invokeHost _ _ _ producerAddress producerType 10 updated _ rfl rfl outcome) [] afterProducer)
  have falls : Step host (iteration (store 2) (values (returned ++ [i64 88, i32 0]) ++ afterProducer))
      (iteration (store 2) (values (returned ++ [i64 88]) ++ [.source .drop])) :=
    inIteration (.context (.pure _ _ (.brIfZero ⟨0⟩)) (returned ++ [i64 88]) [.source .drop])
  have drops : Step host (iteration (store 2) (values (returned ++ [i64 88]) ++ [.source .drop]))
      (iteration (store 2) (values returned)) :=
    inIteration (.context (.pure _ _ (.drop (i64 88))) returned [])
  have completes := (loop.result_iff (host := host) (s := store 2) (f := active)
    (saved := saved) (rest := tail) (payload := returned) rfl rfl).mpr rfl
  have resolves : Step host (function ⟨store 2, active, values (saved ++ returned) ++ tail⟩)
      (function ⟨store 2, active, values (saved ++ returned) ++ [.invoke laterAddress]⟩) :=
    inFunction (.context (.call _ _ ⟨1⟩ laterAddress rfl) (saved ++ returned) [])
  exact (((((reentry.tail (resolvesProducer (store 1) updated)).tail returns).tail falls).tail drops).tail
    (inFunction completes)).tail resolves

-- The later host consumes the i32 result above the saved i64, with the
-- latest memory. The function label and frame then complete separately.
example : Steps host launch ⟨store 2, caller, values [i32 5]⟩ := by
  have outcome : host 11 (store 2) (saved ++ returned) (.returned (store 2) (.values [i32 5])) :=
    .inr (.inr ⟨rfl, rfl, rfl, rfl⟩)
  have resumes := inFunction (.invokeHost _ _ _ laterAddress laterType 11 (saved ++ returned) _ rfl rfl outcome)
  have closes : Step host (function ⟨store 2, active, values [i32 5]⟩)
      ⟨store 2, caller, [.frame 1 active (values [i32 5])]⟩ :=
    .frame (.pure _ _ (.labelDone 1 [] [i32 5])) 1 caller
  exact ((reachesLater.tail resumes).tail closes).tail (.pure _ _ (.frameDone 1 active [i32 5] rfl))

private def missing : LimeIndexedLoop := { loop with index := ⟨1⟩ }

example {dst : Config Nat} :
    ¬ Step host ⟨store 0, active, values (saved ++ original) ++ .source missing.instr :: tail⟩ dst :=
  missing.bad_index rfl

example : ¬ ({ loop with signature := ⟨[.int .i32], [.int .i64]⟩ }).Resolved active := by
  unfold LimeIndexedLoop.Resolved
  decide

example : ¬ loop.Parameters returned := by
  unfold LimeIndexedLoop.Parameters
  decide

example : ¬ loop.Results updated := by
  unfold LimeIndexedLoop.Results
  decide

example : Wasm.V1.BlockType.ofCore? (.typeIdx ⟨0⟩) = none := rfl

end Silmaril.Wasm.Institution.Operational.Loops.IndexedHostExamples
