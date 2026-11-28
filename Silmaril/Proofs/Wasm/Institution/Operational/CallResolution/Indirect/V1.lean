module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.V1.Defs
import Silmaril.Wasm.V1.Execution.Inversion

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Proofs.V1

open Execution.Runtime (Frame Value)
open Wasm.V1.Execution

private theorem first_indirect (stack : List Value) (i : TypeIdx) (tail : List Admin) :
    firstRedex (values stack ++ .source (.callIndirect i) :: tail) = some (.source (.callIndirect i)) := by
  simp only [firstRedex_append, firstRedex_values, Option.none_or]
  rfl

private theorem split_context {vs stack : List Value} {before tail rest : List Admin} {i : TypeIdx}
    (active : firstRedex before ≠ none)
    (source : values vs ++ before ++ tail = values stack ++ .source (.callIndirect i) :: rest) :
    ∃ inside suffix, before = values inside ++ .source (.callIndirect i) :: suffix ∧
      vs ++ inside = stack ∧ suffix ++ tail = rest := by
  have first : firstRedex before = some (.source (.callIndirect i)) := by
    have head := congrArg firstRedex source
    rw [first_indirect] at head
    cases seen : firstRedex before with
    | none => exact (active seen).elim
    | some redex => simpa only [firstRedex_append, firstRedex_values, Option.none_or, seen, Option.some_or] using head
  obtain ⟨inside, suffix, eq⟩ := firstRedex_eq_some first
  have joined : values (vs ++ inside) ++ .source (.callIndirect i) :: (suffix ++ tail) =
      values stack ++ .source (.callIndirect i) :: rest := by
    rw [eq] at source
    simpa only [values_append, List.append_assoc, List.cons_append] using source
  obtain ⟨stackEq, _, restEq⟩ := values_cons_inj (x := .source (.callIndirect i))
    (y := .source (.callIndirect i)) rfl rfl joined
  exact ⟨inside, suffix, eq, stackEq, restEq⟩

private theorem leaf_shape {stack : List Value} {rest : List Admin} {i j : TypeIdx} {c : BitVec 32}
    (source : values [Value.int .i32 c] ++ .source (.callIndirect j) :: [] =
      values stack ++ .source (.callIndirect i) :: rest) :
    stack = [Value.int .i32 c] ∧ j = i ∧ rest = [] := by
  obtain ⟨split, instr, tail⟩ := values_cons_inj (x := .source (.callIndirect j))
    (y := .source (.callIndirect i)) rfl rfl source
  exact ⟨split.symm, Wasm.V1.Instr.callIndirect.inj (Execution.Runtime.AdminInstr.source.inj instr), tail.symm⟩

private theorem readback {H : Type} {host : HostSemantics H} {src dst : Config H} (step : Step host src dst)
    {stack : List Value} {i : TypeIdx} {rest : List Admin}
    (source : src.code = values stack ++ .source (.callIndirect i) :: rest) :
    ∃ saved selector out, stack = saved ++ [Value.int .i32 selector] ∧
      v1Resolve src.store src.frame i selector = some out ∧
      dst = v1Resolved src.store src.frame saved rest out := by
  have leading := (congrArg firstRedex source).trans (first_indirect stack i rest)
  induction step generalizing stack rest with
  | @context s t f g before after step saved tail ih =>
    obtain ⟨inside, suffix, eq, split, rfl⟩ := split_context step.firstRedex_ne_none source
    obtain ⟨keep, c, out, rfl, resolved, next⟩ := ih eq ((congrArg firstRedex eq).trans (first_indirect _ _ _))
    exact ⟨saved ++ keep, c, out, by simp only [← split, List.append_assoc], resolved, by
      simpa only [v1Resolved, values_append, List.append_assoc, List.cons_append] using congrArg
        (fun c : Config H => (⟨c.store, c.frame, values saved ++ c.code ++ tail⟩ : Config H)) next⟩
  | callIndirect s f j c table a fn ft tableFound typeFound entry found same =>
    obtain ⟨rfl, rfl, rfl⟩ := leaf_shape source
    exact ⟨[], c, .resolved a, rfl, by simp [v1Resolve, resolveTable, tableFound, typeFound, entry, found, same], rfl⟩
  | callIndirectBounds s f j c table tableFound entry =>
    obtain ⟨rfl, rfl, rfl⟩ := leaf_shape source
    exact ⟨[], c, .bounds, rfl, by simp [v1Resolve, resolveTable, tableFound, entry], rfl⟩
  | callIndirectNull s f j c table tableFound entry =>
    obtain ⟨rfl, rfl, rfl⟩ := leaf_shape source
    exact ⟨[], c, .null, rfl, by simp [v1Resolve, resolveTable, tableFound, entry], rfl⟩
  | callIndirectType s f j c table a fn ft tableFound typeFound entry found different =>
    obtain ⟨rfl, rfl, rfl⟩ := leaf_shape source
    exact ⟨[], c, .mismatch a, rfl, by simp [v1Resolve, resolveTable, tableFound, typeFound, entry, found, different], rfl⟩
  | pure s f move =>
    cases move <;>
      simp only [values_cons, List.nil_append, List.cons_append, List.append_assoc,
        firstRedex_value_cons, firstRedex_append, firstRedex_values, Option.none_or] at leading <;>
      simp [firstRedex_cons, asValue?] at leading
  | _ =>
    simp only [firstRedex_value_cons, firstRedex_append, firstRedex_values, Option.none_or] at leading
    simp [firstRedex_cons, asValue?] at leading

theorem step_iff {H : Type} {host : HostSemantics H} {s : Store H} {caller : Frame}
    {index : TypeIdx} {selector : BitVec 32} {stack : List Value} {tail : List Admin} {dst : Config H} :
    Step host (v1Source s caller index selector stack tail) dst ↔
      ∃ out, v1Resolve s caller index selector = some out ∧ dst = v1Resolved s caller stack tail out := by
  constructor
  · intro step
    obtain ⟨saved, read, out, split, resolved, eq⟩ := readback step rfl
    obtain ⟨rfl, same⟩ := List.append_inj' split rfl
    cases same
    exact ⟨out, resolved, eq⟩
  · rintro ⟨out, resolved, rfl⟩
    have plug (head : Admin)
        (move : Step host ⟨s, caller, [value (.int .i32 selector), .source (.callIndirect index)]⟩
          ⟨s, caller, [head]⟩) :
        Step host (v1Source s caller index selector stack tail) ⟨s, caller, values stack ++ head :: tail⟩ := by
      simpa only [v1Source, values_append, values_cons, values_nil, List.cons_append, List.nil_append,
        List.append_assoc, List.singleton_append] using move.context stack tail
    cases lookup : frameTable s caller with
    | none => simp [v1Resolve, resolveTable, lookup] at resolved
    | some table =>
      cases element : table.refs[selector.toNat]? with
      | none =>
        simp [v1Resolve, resolveTable, lookup, element] at resolved
        subst out
        exact plug .trap (.callIndirectBounds _ _ _ _ _ lookup element)
      | some entry =>
        cases entry with
        | none =>
          simp [v1Resolve, resolveTable, lookup, element] at resolved
          subst out
          exact plug .trap (.callIndirectNull _ _ _ _ _ lookup element)
        | some address =>
          cases typeFound : caller.module.types[index.toNat]? with
          | none => simp [v1Resolve, resolveTable, lookup, element, typeFound] at resolved
          | some expected =>
            cases allocated : s.funcs[address.value]? with
            | none => simp [v1Resolve, resolveTable, lookup, element, typeFound, allocated] at resolved
            | some fn =>
              by_cases same : fn.type = expected
              · simp [v1Resolve, resolveTable, lookup, element, typeFound, allocated, same] at resolved
                subst out
                exact plug (.invoke address) (.callIndirect _ _ _ _ _ _ _ _ lookup typeFound element allocated same)
              · simp [v1Resolve, resolveTable, lookup, element, typeFound, allocated, same] at resolved
                subst out
                exact plug .trap (.callIndirectType _ _ _ _ _ _ _ _ lookup typeFound element allocated same)

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Proofs.V1
