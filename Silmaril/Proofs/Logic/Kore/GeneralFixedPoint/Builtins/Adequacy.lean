module

public import Silmaril.Proofs.Logic.Kore.FixedPoint.Environment
public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Semantics.Defs
public import Silmaril.Logic.Matching.GeneralFixedPoint.SetObjects.Thms

-- The theorem is uniform over configurable builtin sort bindings.
set_option linter.concreteInstances false
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Proofs.Logic.Kore.GeneralFixedPoint.Builtins
open Silmaril.Logic.Kore.GeneralFixedPoint
open Silmaril.Logic.Kore.GeneralFixedPoint.Builtins
open Silmaril.Logic.Kore.GeneralFixedPoint.Semantics
open Silmaril.Proofs.Logic.Kore.FixedPoint
variable [sorts : SortBindings]
variable {scope : Silmaril.Logic.Kore.Modules.Scope}
variable (aliases : List Alias)
variable (M : Silmaril.Logic.Matching.GeneralFixedPoint.Model scope.signature)

variable (literals : List LiteralBinding)
variable (literalPrefix : String) (hooks : List HookBinding) (B : Carriers M)
variable (laws : Laws M literalPrefix literals hooks B)
include laws

theorem literal_denote (mi : Nat) (l : Literal)
    (op : LiteralOperation scope literals literalPrefix mi l) (sets objects : Names)
    (v : ∀ i, Set (M.carrier (context objects i)))
    (η : ∀ i, Set (M.carrier (context sets i))) :
    (Silmaril.Logic.Matching.GeneralFixedPoint.Pattern.app op.operation (fun i => i.elim0)).denoteSetObjects M v η =
      {B.literal l} := by
  ext x
  change (∃ values, (∀ i : Fin 0, _) ∧ x ∈ M.operation op.operation values) ↔ _
  have tuple (values : ∀ i : Fin 0, M.carrier ((fun i : Fin 0 => i.elim0) i)) :
      values = (fun i => i.elim0) := by funext i; exact i.elim0
  simp only [tuple, laws.literal op.binding op.member l op.value op.operation op.declared]
  constructor
  · rintro ⟨_, _, h⟩; exact h
  · intro h; exact ⟨(fun i => i.elim0), (fun i => i.elim0), h⟩

/-- Accepted named syntax has the native meaning in every model and under
arbitrary object and set valuations. No equation of meanings is assumed. -/
theorem elaborate_sound_setObjects (fuel : Nat) :
    ∀ (mi : Nat) (sets objects : Names) (s : String) (raw : RawPattern)
      (typed : Pattern scope sets objects s)
      (v : ∀ i, Set (M.carrier (context objects i)))
      (η : ∀ i, Set (M.carrier (context sets i))),
      Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Checking.elaborate scope aliases literals literalPrefix mi fuel sets objects s raw = some typed →
      Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Semantics.denote scope aliases M B fuel (interpret M sets η) (interpret M objects v) s raw =
        some (typed.denoteSetObjects M v η) := by
  induction fuel with
  | zero => intros; contradiction
  | succ n ih =>
    intro mi sets objects s raw typed v η accepted
    cases raw with
    | domainValue actual text =>
        simp only [Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Checking.elaborate] at accepted
        split at accepted
        · contradiction
        · rename_i valid
          obtain ⟨l, parsed, rest⟩ := Option.bind_eq_some_iff.mp accepted
          split at rest
          · rename_i same
            cases same
            obtain ⟨op, found, result⟩ := Option.bind_eq_some_iff.mp rest
            cases Option.some.inj result
            simp only [Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Semantics.denote,
              valid, ↓reduceIte, parsed, bind, Option.bind, ↓reduceDIte]
            rw [literal_denote M literals literalPrefix hooks B laws mi l op sets objects v η]
          · contradiction
    | evar name actual =>
        simp only [Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Checking.elaborate] at accepted
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
                simp only [Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Semantics.denote, valid, Bool.false_eq_true, ↓reduceIte, lookup_interpret, found,
                  Option.bind, ↓reduceDIte, Silmaril.Logic.Matching.GeneralFixedPoint.Pattern.denoteSetObjects,
                  Silmaril.Logic.Matching.GeneralFixedPoint.denoteFirstOrderSets]
              · contradiction
    | svar name actual =>
        simp only [Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Checking.elaborate] at accepted
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
                simp only [Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Semantics.denote, valid, Bool.false_eq_true, ↓reduceIte, lookup_interpret, found,
                  Option.bind, ↓reduceDIte, Silmaril.Logic.Matching.GeneralFixedPoint.Pattern.denoteSetObjects]
              · contradiction
    | top actual =>
        simp only [Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Checking.elaborate] at accepted
        split at accepted
        · rename_i valid
          cases Option.some.inj accepted
          simp only [Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Semantics.denote, valid, ↓reduceIte, Silmaril.Logic.Matching.GeneralFixedPoint.Pattern.denoteSetObjects,
            Silmaril.Logic.Matching.FirstOrder.Pattern.top,
            Silmaril.Logic.Matching.GeneralFixedPoint.denoteFirstOrderSets]
          congr 1
          ext x
          simp
        · contradiction
    | bottom actual =>
        simp only [Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Checking.elaborate] at accepted
        split at accepted
        · rename_i valid
          cases Option.some.inj accepted
          simp only [Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Semantics.denote, valid, ↓reduceIte, Silmaril.Logic.Matching.GeneralFixedPoint.Pattern.denoteSetObjects,
            Silmaril.Logic.Matching.FirstOrder.Pattern.bottom,
            Silmaril.Logic.Matching.FirstOrder.Pattern.top,
            Silmaril.Logic.Matching.GeneralFixedPoint.denoteFirstOrderSets]
          congr 1
          ext x
          simp
        · contradiction
    | neg actual body =>
        simp only [Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Checking.elaborate] at accepted
        split at accepted
        · contradiction
        · rename_i valid
          obtain ⟨p, hp, result⟩ := Option.bind_eq_some_iff.mp accepted
          cases Option.some.inj result
          simp only [Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Semantics.denote, valid, ↓reduceIte, ih mi sets objects s body p v η hp,
            bind, Option.bind, Silmaril.Logic.Matching.GeneralFixedPoint.Pattern.denoteSetObjects]
          rfl
    | conj actual left right =>
        simp only [Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Checking.elaborate] at accepted
        split at accepted
        · contradiction
        · rename_i valid
          obtain ⟨p, hp, rest⟩ := Option.bind_eq_some_iff.mp accepted
          obtain ⟨q, hq, result⟩ := Option.bind_eq_some_iff.mp rest
          cases Option.some.inj result
          simp only [Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Semantics.denote, valid, ↓reduceIte, ih mi sets objects s left p v η hp,
            ih mi sets objects s right q v η hq, bind, Option.bind, Silmaril.Logic.Matching.GeneralFixedPoint.Pattern.denoteSetObjects]
          rfl
    | disj actual left right =>
        simp only [Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Checking.elaborate] at accepted
        split at accepted
        · contradiction
        · rename_i valid
          obtain ⟨p, hp, rest⟩ := Option.bind_eq_some_iff.mp accepted
          obtain ⟨q, hq, result⟩ := Option.bind_eq_some_iff.mp rest
          cases Option.some.inj result
          simp only [Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Semantics.denote, valid, ↓reduceIte, ih mi sets objects s left p v η hp,
            ih mi sets objects s right q v η hq, bind, Option.bind, Silmaril.Logic.Matching.GeneralFixedPoint.Pattern.disj,
            Silmaril.Logic.Matching.GeneralFixedPoint.Pattern.denoteSetObjects]
          congr 1
          ext x
          simp
    | ex actual name b body =>
        simp only [Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Checking.elaborate] at accepted
        split at accepted
        · contradiction
        · rename_i valid
          obtain ⟨p, hp, result⟩ := Option.bind_eq_some_iff.mp accepted
          cases Option.some.inj result
          have bodyMeaning (x : M.carrier b) :
              Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Semantics.denote scope aliases M B n (interpret M sets η) (⟨name, b, {x}⟩ ::
                interpret M objects v) s body =
                some (p.denoteSetObjects M (@Fin.cases objects.length (fun i => Set (M.carrier (context ((name, b) :: objects) i))) {x} v) η) := by
            simpa only [interpret, Silmaril.Logic.Kore.FixedPoint.Semantics.interpret, Fin.cases_zero, Fin.cases_succ] using
              ih mi sets ((name, b) :: objects) s body p (@Fin.cases objects.length (fun i => Set (M.carrier (context ((name, b) :: objects) i))) {x} v) η hp
          with_unfolding_all simp only [Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Semantics.denote, valid, Bool.false_eq_true, ↓reduceIte, bodyMeaning, Option.getD_some,
            Silmaril.Logic.Matching.GeneralFixedPoint.Pattern.denoteSetObjects]
    | all actual name b body =>
        simp only [Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Checking.elaborate] at accepted
        split at accepted
        · contradiction
        · rename_i valid
          obtain ⟨p, hp, result⟩ := Option.bind_eq_some_iff.mp accepted
          cases Option.some.inj result
          have bodyMeaning (x : M.carrier b) :
              Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Semantics.denote scope aliases M B n (interpret M sets η) (⟨name, b, {x}⟩ ::
                interpret M objects v) s body =
                some (p.denoteSetObjects M (@Fin.cases objects.length (fun i => Set (M.carrier (context ((name, b) :: objects) i))) {x} v) η) := by
            simpa only [interpret, Silmaril.Logic.Kore.FixedPoint.Semantics.interpret, Fin.cases_zero, Fin.cases_succ] using
              ih mi sets ((name, b) :: objects) s body p (@Fin.cases objects.length (fun i => Set (M.carrier (context ((name, b) :: objects) i))) {x} v) η hp
          with_unfolding_all simp only [Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Semantics.denote, valid, Bool.false_eq_true, ↓reduceIte, bodyMeaning, Option.getD_some,
            Silmaril.Logic.Matching.GeneralFixedPoint.Pattern.all,
            Silmaril.Logic.Matching.GeneralFixedPoint.Pattern.denoteSetObjects]
          congr 1
          ext x
          simp
    | mu name actual body =>
        simp only [Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Checking.elaborate] at accepted
        with_unfolding_all split at accepted
        · contradiction
        · rename_i valid
          obtain ⟨p, hp, result⟩ := Option.bind_eq_some_iff.mp accepted
          cases Option.some.inj result
          have bodyMeaning (X : Set (M.carrier s)) :
              Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Semantics.denote scope aliases M B n (⟨name, s, X⟩ :: interpret M sets η)
                (interpret M objects v) s body =
                some (p.denoteSetObjects M v (@Fin.cases sets.length (fun i => Set (M.carrier (context ((name, s) :: sets) i))) X η)) := by
            simpa only [interpret, Silmaril.Logic.Kore.FixedPoint.Semantics.interpret, Fin.cases_zero, Fin.cases_succ] using
              ih mi ((name, s) :: sets) objects s body p v (@Fin.cases sets.length (fun i => Set (M.carrier (context ((name, s) :: sets) i))) X η) hp
          with_unfolding_all simp only [Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Semantics.denote, valid, Bool.false_eq_true, ↓reduceIte, bodyMeaning, Option.getD_some,
            Silmaril.Logic.Matching.GeneralFixedPoint.Pattern.denoteSetObjects]
          rfl
    | nu name actual body =>
        simp only [Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Checking.elaborate] at accepted
        with_unfolding_all split at accepted
        · contradiction
        · rename_i valid
          obtain ⟨p, hp, result⟩ := Option.bind_eq_some_iff.mp accepted
          cases Option.some.inj result
          have bodyMeaning (X : Set (M.carrier s)) :
              Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Semantics.denote scope aliases M B n (⟨name, s, X⟩ :: interpret M sets η)
                (interpret M objects v) s body =
                some (p.denoteSetObjects M v (@Fin.cases sets.length (fun i => Set (M.carrier (context ((name, s) :: sets) i))) X η)) := by
            simpa only [interpret, Silmaril.Logic.Kore.FixedPoint.Semantics.interpret, Fin.cases_zero, Fin.cases_succ] using
              ih mi ((name, s) :: sets) objects s body p v (@Fin.cases sets.length (fun i => Set (M.carrier (context ((name, s) :: sets) i))) X η) hp
          with_unfolding_all simp only [Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Semantics.denote, valid, Bool.false_eq_true, ↓reduceIte, bodyMeaning, Option.getD_some,
            Silmaril.Logic.Matching.GeneralFixedPoint.Pattern.denoteSetObjects]
          rfl
    | app name args =>
        simp only [Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Checking.elaborate] at accepted
        cases found : scope.symbols.attach.find? (fun d => d.val.declaration.name == name) with
        | none =>
            simp only [found] at accepted
            cases aliasFound : aliases.find? (fun d => d.symbol.name == name) with
            | none => simp [aliasFound] at accepted
            | some d =>
                simp only [aliasFound, bind, Option.bind] at accepted
                split at accepted
                · rename_i valid
                  obtain ⟨body, hbody, rest⟩ := Option.bind_eq_some_iff.mp accepted
                  obtain ⟨σ, hσ, rest⟩ := Option.bind_eq_some_iff.mp rest
                  obtain ⟨τ, hτ, result⟩ := Option.bind_eq_some_iff.mp rest
                  cases Option.some.inj result
                  have objectsMeaning (i : Fin (d.names false).length) :
                      (do
                        let arg ← d.argument args false ((d.names false).get i).1
                        Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Semantics.denote scope aliases M B n
                          (interpret M sets η) (interpret M objects v)
                          (context (d.names false) i) arg) =
                        some ((σ i).denoteSetObjects M v η) := by
                    obtain ⟨arg, harg, htyped⟩ := Option.bind_eq_some_iff.mp (collect_some _ _ hσ i)
                    simp only [harg, bind, Option.bind]
                    exact ih mi sets objects _ arg (σ i) v η htyped
                  have setsMeaning (i : Fin (d.names true).length) :
                      (do
                        let arg ← d.argument args true ((d.names true).get i).1
                        Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Semantics.denote scope aliases M B n
                          (interpret M sets η) (interpret M objects v)
                          (context (d.names true) i) arg) =
                        some ((τ i).denoteSetObjects M v η) := by
                    obtain ⟨arg, harg, htyped⟩ := Option.bind_eq_some_iff.mp (collect_some _ _ hτ i)
                    simp only [harg, bind, Option.bind]
                    exact ih mi sets objects _ arg (τ i) v η htyped
                  have objectsCollected :
                      Silmaril.Logic.Kore.Modules.Checking.collect
                        (fun i : Fin (d.names false).length => do
                          let arg ← d.argument args false ((d.names false).get i).1
                          Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Semantics.denote scope aliases M B n
                            (interpret M sets η) (interpret M objects v)
                            (context (d.names false) i) arg) =
                        some (fun i => (σ i).denoteSetObjects M v η) := by
                    simp only [objectsMeaning, collect_pure]
                  have setsCollected :
                      Silmaril.Logic.Kore.Modules.Checking.collect
                        (fun i : Fin (d.names true).length => do
                          let arg ← d.argument args true ((d.names true).get i).1
                          Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Semantics.denote scope aliases M B n
                            (interpret M sets η) (interpret M objects v)
                            (context (d.names true) i) arg) =
                        some (fun i => (τ i).denoteSetObjects M v η) := by
                    simp only [setsMeaning, collect_pure]
                  simp only [bind, Option.bind] at objectsCollected setsCollected
                  have bodyMeaning := ih d.moduleIndex (d.names true) (d.names false) s d.body body
                    (fun i => (σ i).denoteSetObjects M v η)
                    (fun i => (τ i).denoteSetObjects M v η) hbody
                  simp only [Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Semantics.denote,
                    found, aliasFound, bind, Option.bind, valid, ↓reduceIte]
                  rw [objectsCollected]
                  dsimp only [bind, Option.bind]
                  rw [setsCollected]
                  dsimp only [bind, Option.bind]
                  rw [bodyMeaning]
                  congr 1
                  exact (body.denoteSetObjects_substitute M τ σ v η _ (fun _ => rfl)).symm
                · contradiction
        | some d =>
            simp only [found, bind, Option.bind] at accepted
            split at accepted
            · rename_i outputSort
              split at accepted
              · rename_i arity
                obtain ⟨ps, hps, result⟩ := Option.bind_eq_some_iff.mp accepted
                cases Option.some.inj result
                have argumentMeaning (i : Fin d.val.declaration.arguments.length) :
                    Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Semantics.denote scope aliases M B n (interpret M sets η) (interpret M objects v)
                      (d.val.declaration.arguments.get i) (args.get ⟨i.val, by omega⟩) =
                      some ((ps i).denoteSetObjects M v η) :=
                  ih mi sets objects _ _ _ v η (collect_some _ _ hps i)
                simp only [Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Semantics.denote, found, bind, Option.bind, outputSort, arity, ↓reduceDIte,
                  argumentMeaning, collect_pure, Silmaril.Logic.Matching.GeneralFixedPoint.Pattern.denoteSetObjects]
                rfl
              · contradiction
            · contradiction
/-- Ordinary source sentences retain singleton element valuations. Alias formals
may still denote arbitrary sets internally. -/
theorem elaborate_sound (fuel mi : Nat) (sets objects : Names) (s : String)
    (raw : RawPattern) (typed : Pattern scope sets objects s)
    (v : ∀ i, M.carrier (context objects i))
    (η : ∀ i, Set (M.carrier (context sets i)))
    (accepted : Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Checking.elaborate
      scope aliases literals literalPrefix mi fuel sets objects s raw = some typed) :
    Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Semantics.denote scope aliases M B fuel
      (interpret M sets η) (interpret M objects (fun i => {v i})) s raw =
      some (typed.denote M v η) := by
  rw [elaborate_sound_setObjects aliases M literals literalPrefix hooks B laws fuel mi sets objects s raw typed _ η accepted,
    Silmaril.Logic.Matching.GeneralFixedPoint.Pattern.denoteSetObjects_singleton]

end Silmaril.Proofs.Logic.Kore.GeneralFixedPoint.Builtins
