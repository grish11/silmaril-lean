module

public import Silmaril.Proofs.Logic.Kore.FixedPoint.Environment
public import Silmaril.Logic.Kore.GeneralFixedPoint.Semantics.Defs
public import Silmaril.Logic.Matching.GeneralFixedPoint.SetObjects.Thms

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Proofs.Logic.Kore.GeneralFixedPoint
open Silmaril.Logic.Kore.GeneralFixedPoint Silmaril.Logic.Kore.GeneralFixedPoint.Semantics
open Silmaril.Proofs.Logic.Kore.FixedPoint
variable {scope : Silmaril.Logic.Kore.Modules.Scope}
variable (M : Silmaril.Logic.Matching.GeneralFixedPoint.Model scope.signature)

/-- Accepted named syntax has the native meaning in every model and under
arbitrary object and set valuations. No equation of meanings is assumed. -/
theorem elaborate_sound_setObjects (fuel : Nat) :
    ∀ (sets objects : Names) (s : String) (raw : RawPattern)
      (typed : Pattern scope sets objects s)
      (v : ∀ i, Set (M.carrier (context objects i)))
      (η : ∀ i, Set (M.carrier (context sets i))),
      Checking.elaborate scope fuel sets objects s raw = some typed →
      denote scope M fuel (interpret M sets η) (interpret M objects v) s raw =
        some (typed.denoteSetObjects M v η) := by
  induction fuel with
  | zero => intros; contradiction
  | succ n ih =>
    intro sets objects s raw typed v η accepted
    cases raw with
    | domainValue _ _ => contradiction
    | evar name actual =>
        simp only [Checking.elaborate] at accepted
        split at accepted
        · contradiction
        · rename_i valid
          cases found : lookup objects name with
          | none => simp [found] at accepted
          | some i =>
              simp only [found, bind, Option.bind] at accepted
              split at accepted
              · rename_i same
                cases same
                cases Option.some.inj accepted
                simp only [denote, valid, Bool.false_eq_true, ↓reduceIte, lookup_interpret, found,
                  Option.bind, ↓reduceDIte, Silmaril.Logic.Matching.GeneralFixedPoint.Pattern.denoteSetObjects,
                  Silmaril.Logic.Matching.GeneralFixedPoint.denoteFirstOrderSets]
              · contradiction
    | svar name actual =>
        simp only [Checking.elaborate] at accepted
        split at accepted
        · contradiction
        · rename_i valid
          cases found : lookup sets name with
          | none => simp [found] at accepted
          | some i =>
              simp only [found, bind, Option.bind] at accepted
              split at accepted
              · rename_i same
                cases same
                cases Option.some.inj accepted
                simp only [denote, valid, Bool.false_eq_true, ↓reduceIte, lookup_interpret, found,
                  Option.bind, ↓reduceDIte, Silmaril.Logic.Matching.GeneralFixedPoint.Pattern.denoteSetObjects]
              · contradiction
    | top actual =>
        simp only [Checking.elaborate] at accepted
        split at accepted
        · rename_i valid
          cases Option.some.inj accepted
          simp only [denote, valid, ↓reduceIte, Silmaril.Logic.Matching.GeneralFixedPoint.Pattern.denoteSetObjects,
            Silmaril.Logic.Matching.FirstOrder.Pattern.top,
            Silmaril.Logic.Matching.GeneralFixedPoint.denoteFirstOrderSets]
          congr 1
          ext x
          simp
        · contradiction
    | bottom actual =>
        simp only [Checking.elaborate] at accepted
        split at accepted
        · rename_i valid
          cases Option.some.inj accepted
          simp only [denote, valid, ↓reduceIte, Silmaril.Logic.Matching.GeneralFixedPoint.Pattern.denoteSetObjects,
            Silmaril.Logic.Matching.FirstOrder.Pattern.bottom,
            Silmaril.Logic.Matching.FirstOrder.Pattern.top,
            Silmaril.Logic.Matching.GeneralFixedPoint.denoteFirstOrderSets]
          congr 1
          ext x
          simp
        · contradiction
    | neg actual body =>
        simp only [Checking.elaborate] at accepted
        split at accepted
        · contradiction
        · rename_i valid
          obtain ⟨p, hp, result⟩ := Option.bind_eq_some_iff.mp accepted
          cases Option.some.inj result
          simp only [denote, valid, ↓reduceIte, ih sets objects s body p v η hp,
            bind, Option.bind, Silmaril.Logic.Matching.GeneralFixedPoint.Pattern.denoteSetObjects]
          rfl
    | conj actual left right =>
        simp only [Checking.elaborate] at accepted
        split at accepted
        · contradiction
        · rename_i valid
          obtain ⟨p, hp, rest⟩ := Option.bind_eq_some_iff.mp accepted
          obtain ⟨q, hq, result⟩ := Option.bind_eq_some_iff.mp rest
          cases Option.some.inj result
          simp only [denote, valid, ↓reduceIte, ih sets objects s left p v η hp,
            ih sets objects s right q v η hq, bind, Option.bind, Silmaril.Logic.Matching.GeneralFixedPoint.Pattern.denoteSetObjects]
          rfl
    | disj actual left right =>
        simp only [Checking.elaborate] at accepted
        split at accepted
        · contradiction
        · rename_i valid
          obtain ⟨p, hp, rest⟩ := Option.bind_eq_some_iff.mp accepted
          obtain ⟨q, hq, result⟩ := Option.bind_eq_some_iff.mp rest
          cases Option.some.inj result
          simp only [denote, valid, ↓reduceIte, ih sets objects s left p v η hp,
            ih sets objects s right q v η hq, bind, Option.bind, Silmaril.Logic.Matching.GeneralFixedPoint.Pattern.disj,
            Silmaril.Logic.Matching.GeneralFixedPoint.Pattern.denoteSetObjects]
          congr 1
          ext x
          simp
    | ex actual name b body =>
        simp only [Checking.elaborate] at accepted
        split at accepted
        · contradiction
        · rename_i valid
          obtain ⟨p, hp, result⟩ := Option.bind_eq_some_iff.mp accepted
          cases Option.some.inj result
          have bodyMeaning (x : M.carrier b) :
              denote scope M n (interpret M sets η) (⟨name, b, {x}⟩ ::
                interpret M objects v) s body =
                some (p.denoteSetObjects M (@Fin.cases objects.length (fun i => Set (M.carrier (context ((name, b) :: objects) i))) {x} v) η) := by
            simpa only [interpret, Silmaril.Logic.Kore.FixedPoint.Semantics.interpret, Fin.cases_zero, Fin.cases_succ] using
              ih sets ((name, b) :: objects) s body p (@Fin.cases objects.length (fun i => Set (M.carrier (context ((name, b) :: objects) i))) {x} v) η hp
          with_unfolding_all simp only [denote, valid, Bool.false_eq_true, ↓reduceIte, bodyMeaning, Option.getD_some,
            Silmaril.Logic.Matching.GeneralFixedPoint.Pattern.denoteSetObjects]
    | all actual name b body =>
        simp only [Checking.elaborate] at accepted
        split at accepted
        · contradiction
        · rename_i valid
          obtain ⟨p, hp, result⟩ := Option.bind_eq_some_iff.mp accepted
          cases Option.some.inj result
          have bodyMeaning (x : M.carrier b) :
              denote scope M n (interpret M sets η) (⟨name, b, {x}⟩ ::
                interpret M objects v) s body =
                some (p.denoteSetObjects M (@Fin.cases objects.length (fun i => Set (M.carrier (context ((name, b) :: objects) i))) {x} v) η) := by
            simpa only [interpret, Silmaril.Logic.Kore.FixedPoint.Semantics.interpret, Fin.cases_zero, Fin.cases_succ] using
              ih sets ((name, b) :: objects) s body p (@Fin.cases objects.length (fun i => Set (M.carrier (context ((name, b) :: objects) i))) {x} v) η hp
          with_unfolding_all simp only [denote, valid, Bool.false_eq_true, ↓reduceIte, bodyMeaning, Option.getD_some,
            Silmaril.Logic.Matching.GeneralFixedPoint.Pattern.all,
            Silmaril.Logic.Matching.GeneralFixedPoint.Pattern.denoteSetObjects]
          congr 1
          ext x
          simp
    | mu name actual body =>
        simp only [Checking.elaborate] at accepted
        with_unfolding_all split at accepted
        · contradiction
        · rename_i valid
          obtain ⟨p, hp, result⟩ := Option.bind_eq_some_iff.mp accepted
          cases Option.some.inj result
          have bodyMeaning (X : Set (M.carrier s)) :
              denote scope M n (⟨name, s, X⟩ :: interpret M sets η)
                (interpret M objects v) s body =
                some (p.denoteSetObjects M v (@Fin.cases sets.length (fun i => Set (M.carrier (context ((name, s) :: sets) i))) X η)) := by
            simpa only [interpret, Silmaril.Logic.Kore.FixedPoint.Semantics.interpret, Fin.cases_zero, Fin.cases_succ] using
              ih ((name, s) :: sets) objects s body p v (@Fin.cases sets.length (fun i => Set (M.carrier (context ((name, s) :: sets) i))) X η) hp
          with_unfolding_all simp only [denote, valid, Bool.false_eq_true, ↓reduceIte, bodyMeaning, Option.getD_some,
            Silmaril.Logic.Matching.GeneralFixedPoint.Pattern.denoteSetObjects]
          rfl
    | nu name actual body =>
        simp only [Checking.elaborate] at accepted
        with_unfolding_all split at accepted
        · contradiction
        · rename_i valid
          obtain ⟨p, hp, result⟩ := Option.bind_eq_some_iff.mp accepted
          cases Option.some.inj result
          have bodyMeaning (X : Set (M.carrier s)) :
              denote scope M n (⟨name, s, X⟩ :: interpret M sets η)
                (interpret M objects v) s body =
                some (p.denoteSetObjects M v (@Fin.cases sets.length (fun i => Set (M.carrier (context ((name, s) :: sets) i))) X η)) := by
            simpa only [interpret, Silmaril.Logic.Kore.FixedPoint.Semantics.interpret, Fin.cases_zero, Fin.cases_succ] using
              ih ((name, s) :: sets) objects s body p v (@Fin.cases sets.length (fun i => Set (M.carrier (context ((name, s) :: sets) i))) X η) hp
          with_unfolding_all simp only [denote, valid, Bool.false_eq_true, ↓reduceIte, bodyMeaning, Option.getD_some,
            Silmaril.Logic.Matching.GeneralFixedPoint.Pattern.denoteSetObjects]
          rfl
    | app name args =>
        simp only [Checking.elaborate] at accepted
        cases found : scope.symbols.attach.find? (fun d => d.val.declaration.name == name) with
        | none => simp [found] at accepted
        | some d =>
            simp only [found, bind, Option.bind] at accepted
            split at accepted
            · rename_i outputSort
              split at accepted
              · rename_i arity
                obtain ⟨ps, hps, result⟩ := Option.bind_eq_some_iff.mp accepted
                cases Option.some.inj result
                have argumentMeaning (i : Fin d.val.declaration.arguments.length) :
                    denote scope M n (interpret M sets η) (interpret M objects v)
                      (d.val.declaration.arguments.get i) (args.get ⟨i.val, by omega⟩) =
                      some ((ps i).denoteSetObjects M v η) :=
                  ih sets objects _ _ _ v η (collect_some _ _ hps i)
                simp only [denote, found, bind, Option.bind, outputSort, arity, ↓reduceDIte,
                  argumentMeaning, collect_pure, Silmaril.Logic.Matching.GeneralFixedPoint.Pattern.denoteSetObjects]
                rfl
              · contradiction
            · contradiction
end Silmaril.Proofs.Logic.Kore.GeneralFixedPoint
