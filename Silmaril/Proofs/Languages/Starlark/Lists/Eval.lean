module

public import Silmaril.Languages.Starlark.Lists.Denotation.Defs
public import Silmaril.Languages.Starlark.Lists.Operational.Defs

public section

namespace Silmaril.Proofs.Languages.Starlark.Lists

open Silmaril.Languages.Starlark.Lists

private theorem runBind {α β : Type} (first : Meaning α) (next : α → Meaning β)
    (state : State) : (first >>= next) state = Outcome.resume (first state) next := by
  cases h : first state <;> simp [bind, EStateM.bind, Outcome.resume, h]

private theorem runMap {α β : Type} (f : α → β) (first : Meaning α) (state : State) :
    (f <$> first) state = Outcome.resume (first state) (fun value => pure (f value)) := by
  cases h : first state <;> simp [Functor.map, EStateM.map, Outcome.resume, h] <;> rfl

theorem denote_eq_of_eval {α : Type} {s : State} {code : Code α} {out : Outcome α}
    (h : Eval s code out) : denote code s = out := by
  induction h <;> simp_all [denote, runBind, runMap, Outcome.resume]
  case appendTargetError value _ _ _ =>
    cases value <;> simp_all <;> rfl
  all_goals rfl

theorem eval_denote {α : Type} (code : Code α) (state : State) :
    Eval state code (denote code state) := by
  induction code generalizing state with
  | scalar => exact .scalar
  | builtin => exact .builtin
  | string => exact .string
  | read => exact .read
  | list elements ih => simpa [denote, runBind] using Eval.list (ih state)
  | tuple elements ih => simpa [denote, runBind] using Eval.tuple (ih state)
  | dict entries ih => simpa [denote, runBind] using Eval.dict (ih state)
  | noEntries => exact .noEntries
  | entry earlier key value ihPrefix ihKey ihValue =>
    cases hp : denote earlier state with
    | error error next =>
      simpa [denote, runBind, Outcome.resume, hp] using
        Eval.entryPrefixError (key := key) (value := value) (hp ▸ ihPrefix state)
    | ok entries next =>
      cases hk : denote key next with
      | error error after =>
        simpa [denote, runBind, Outcome.resume, hp, hk] using
          Eval.entryKeyError (value := value) (hp ▸ ihPrefix state) (hk ▸ ihKey next)
      | ok k after =>
        simpa [denote, runBind, Outcome.resume, hp, hk] using
          Eval.entry (hp ▸ ihPrefix state) (hk ▸ ihKey next) (ihValue after)
  | empty => exact .empty
  | cons head tail ihHead ihTail =>
    cases h : denote head state with
    | error error next =>
      simpa [denote, runBind, Outcome.resume, h] using Eval.consError (tail := tail) (h ▸ ihHead state)
    | ok value next =>
      simpa [denote, runBind, runMap, Outcome.resume, h] using
        Eval.cons (h ▸ ihHead state) (ihTail next)
  | index receiver index ihReceiver ihIndex =>
    cases h : denote receiver state with
    | error error next =>
      simpa [denote, runBind, Outcome.resume, h] using
        Eval.indexReceiverError (index := index) (h ▸ ihReceiver state)
    | ok value next =>
      simpa [denote, runBind, Outcome.resume, h] using Eval.index (h ▸ ihReceiver state) (ihIndex next)
  | append receiver argument ihReceiver ihArgument =>
    cases h : denote receiver state with
    | error error next =>
      simpa [denote, runBind, Outcome.resume, h] using
        Eval.appendReceiverError (argument := argument) (h ▸ ihReceiver state)
    | ok value next =>
      cases value with
      | scalar | tuple | dict | function | builtin | string =>
        rw [denote, runBind, h]
        exact Eval.appendTargetError (h ▸ ihReceiver state) (by intro _ equality; cases equality)
      | list address =>
        simpa [denote, runBind, Outcome.resume, h] using
          Eval.append (h ▸ ihReceiver state) (ihArgument next)
  | pass => exact .pass
  | eval expr ih => simpa [denote, runBind] using Eval.eval (ih state)
  | assign binding rhs ih => simpa [denote, runBind] using Eval.assign (binding := binding) (ih state)
  | setIndex receiver index rhs ihReceiver ihIndex ihRhs =>
    cases hRhs : denote rhs state with
    | error error next =>
      simpa [denote, runBind, Outcome.resume, hRhs] using
        Eval.setIndexRhsError (receiver := receiver) (index := index) (hRhs ▸ ihRhs state)
    | ok value next =>
      cases hReceiver : denote receiver next with
      | error error after =>
        simpa [denote, runBind, Outcome.resume, hRhs, hReceiver] using
          Eval.setIndexReceiverError (index := index) (hRhs ▸ ihRhs state)
            (hReceiver ▸ ihReceiver next)
      | ok target after =>
        simpa [denote, runBind, Outcome.resume, hRhs, hReceiver] using
          Eval.setIndex (hRhs ▸ ihRhs state) (hReceiver ▸ ihReceiver next) (ihIndex after)
  | seq first rest ihFirst ihRest =>
    cases h : denote first state with
    | error error next =>
      simpa [denote, runBind, Outcome.resume, h] using Eval.seqError (rest := rest) (h ▸ ihFirst state)
    | ok value next =>
      cases value
      simpa [denote, runBind, Outcome.resume, h] using Eval.seq (h ▸ ihFirst state) (ihRest next)

end Silmaril.Proofs.Languages.Starlark.Lists
