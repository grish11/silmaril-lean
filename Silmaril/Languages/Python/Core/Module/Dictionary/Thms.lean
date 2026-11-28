module

public import Silmaril.Languages.Python.Core.Module.Dictionary.Defs
import Silmaril.Proofs.Languages.Python.Core.Module.Dictionary.Equality

public section

namespace Silmaril.Languages.Python.Core.Module.Dictionary

theorem insert_replaces {first entry : Entry} (rest : List Entry)
    (same : first.1.equal entry.1 = true) :
    insert entry (first :: rest) = (first.1, entry.2) :: rest := by simp [insert, same]

theorem insert_keeps {first entry : Entry} (rest : List Entry)
    (different : first.1.equal entry.1 = false) :
    insert entry (first :: rest) = first :: insert entry rest := by simp [insert, different]

theorem build_snoc (display : List Entry) (entry : Entry) :
    build (display ++ [entry]) = insert entry (build display) := by simp [build, List.foldl_append]

theorem equalContents_iff {left right : List Entry} :
    equalContents left right = true ↔
      (∀ entry ∈ left, ∃ other ∈ right, entry.equal other = true) ∧
      (∀ entry ∈ right, ∃ other ∈ left, entry.equal other = true) := by
  simp [equalContents, List.all_eq_true, List.any_eq_true]

theorem equalContents_perm {left left' right right' : List Entry}
    (lhs : left.Perm left') (rhs : right.Perm right') :
    equalContents left right = equalContents left' right' := by
  apply Bool.eq_iff_iff.mpr
  simp only [equalContents_iff, lhs.mem_iff, rhs.mem_iff]

theorem equalContents_self (entries : List Entry) : equalContents entries entries = true :=
  Proofs.Languages.Python.Core.Module.Dictionary.equalContents_self entries

theorem Get.eval_missing (test : Get) (globals : String → Option ReadValue)
    (resolve : Object → Option (List Entry)) (missing : globals test.receiver = none) :
    test.eval globals resolve = .error (.missingName test.receiver) := by simp [Get.eval, readName, missing, bind, Except.bind]

theorem Get.eval_default_error (test : Get) (globals : String → Option ReadValue)
    (resolve : Object → Option (List Entry)) (object : Object) (entries : List Entry) (key : ReadValue)
    (found : globals test.receiver = some (.object object)) (live : resolve object = some entries)
    (prepared : test.key.read globals = .ok key) {error : Failure}
    (failed : test.fallback.read globals = .error error) :
    test.eval globals resolve = .error error := by simp [Get.eval, readName, found, live, prepared, failed, bind, Except.bind]

theorem Clear.prepare_zero (globals : String → Option ReadValue) (resolve : Object → Option (List Entry))
    {receiver : String} {object : Object} {entries : List Entry}
    (found : globals receiver = some (.object object)) (live : resolve object = some entries) :
    (⟨receiver, []⟩ : Clear).prepare globals resolve = .ok object := by
  simp [Clear.prepare, readName, found, live, bind, Except.bind, pure, Except.pure]

theorem Clear.prepare_receiverError (call : Clear) (globals : String → Option ReadValue)
    (resolve : Object → Option (List Entry)) {error : Failure}
    (failed : readName globals call.receiver = .error error) : call.prepare globals resolve = .error error := by
  simp [Clear.prepare, failed, bind, Except.bind]

theorem Clear.prepare_argumentError (call : Clear) (globals : String → Option ReadValue)
    (resolve : Object → Option (List Entry)) {object : Object} {entries : List Entry} {error : Failure}
    (found : globals call.receiver = some (.object object)) (live : resolve object = some entries)
    (failed : call.arguments.mapM (Argument.read globals) = .error error) :
    call.prepare globals resolve = .error error := by
  simp [Clear.prepare, readName, found, live, failed, bind, Except.bind]

theorem Clear.prepare_wrongReceiver (call : Clear) (globals : String → Option ReadValue)
    (resolve : Object → Option (List Entry)) {atom : Atom}
    (found : globals call.receiver = some (.atom atom)) : call.prepare globals resolve = .error .unsupported := by
  simp [Clear.prepare, readName, found, bind, Except.bind]
  rfl

theorem Clear.prepare_arity (call : Clear) (globals : String → Option ReadValue)
    (resolve : Object → Option (List Entry)) {object : Object} {entries : List Entry} {first : ReadValue}
    {rest : List ReadValue} (found : globals call.receiver = some (.object object))
    (live : resolve object = some entries) (prepared : call.arguments.mapM (Argument.read globals) = .ok (first :: rest)) :
    call.prepare globals resolve = .error (.clearArity (rest.length + 1)) := by
  simp [Clear.prepare, readName, found, live, prepared, bind, Except.bind]
  rfl

end Silmaril.Languages.Python.Core.Module.Dictionary
