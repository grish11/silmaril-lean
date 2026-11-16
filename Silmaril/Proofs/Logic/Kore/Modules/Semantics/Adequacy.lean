module

public import Silmaril.Proofs.Logic.Kore.Modules.Semantics.Environment

@[expose] public section
namespace Silmaril.Proofs.Logic.Kore.Modules.Semantics
open Silmaril.Logic.Kore Silmaril.Logic.Kore.Modules
open Silmaril.Logic.Kore.Modules.Semantics
variable {scope : Scope} (M : Silmaril.Logic.Matching.FirstOrder.Model scope.signature)

/-- General source adequacy, for arbitrary actual arguments/environments, aliases,
contexts, sorts and raw patterns. Raw denotation does not call the elaborator. -/
theorem elaborate_sound (fuel : Nat) :
    ∀ {k : Nat} {Γ : Fin k → String}
      (vs : List (Checking.Binding scope.signature Γ))
      (v : (i : Fin k) → M.carrier (Γ i)) (s : String) (raw : RawPattern)
      (typed : FirstOrder.Pattern scope.signature Γ s),
      Checking.elaborate scope fuel vs s raw = some typed →
      denote M fuel (interpret M vs v) s raw = FirstOrder.denote scope.signature M v typed := by
  induction fuel with
  | zero => intros; contradiction
  | succ n ih =>
    intro k Γ vs v s raw typed accepted
    cases raw with
    | «variable» name actual =>
        simp only [Checking.elaborate] at accepted
        split at accepted
        · rename_i valid
          simpa only [denote, valid, ↓reduceIte] using lookup_correct M vs v name s typed accepted
        · contradiction
    | top actual =>
        simp only [Checking.elaborate] at accepted
        split at accepted
        · rename_i valid
          cases accepted
          simp only [denote, valid, ↓reduceIte, FirstOrder.denote]
        · contradiction
    | bottom actual =>
        simp only [Checking.elaborate] at accepted
        split at accepted
        · cases accepted; simp only [denote, ite_self, FirstOrder.denote]
        · contradiction
    | not actual body =>
        simp only [Checking.elaborate] at accepted
        split at accepted
        · contradiction
        · rename_i valid
          obtain ⟨p, hp, result⟩ := Option.bind_eq_some_iff.mp accepted
          have eq := Option.some.inj result
          subst typed
          simp only [denote, valid, ↓reduceIte, FirstOrder.denote, ih vs v s body p hp]
    | and actual left right =>
        simp only [Checking.elaborate] at accepted
        split at accepted
        · contradiction
        · rename_i valid
          obtain ⟨p, hp, rest⟩ := Option.bind_eq_some_iff.mp accepted
          obtain ⟨q, hq, result⟩ := Option.bind_eq_some_iff.mp rest
          have eq := Option.some.inj result
          subst typed
          simp only [denote, valid, ↓reduceIte, FirstOrder.denote,
            ih vs v s left p hp, ih vs v s right q hq]
    | or actual left right =>
        simp only [Checking.elaborate] at accepted
        split at accepted
        · contradiction
        · rename_i valid
          obtain ⟨p, hp, rest⟩ := Option.bind_eq_some_iff.mp accepted
          obtain ⟨q, hq, result⟩ := Option.bind_eq_some_iff.mp rest
          have eq := Option.some.inj result
          subst typed
          simp only [denote, valid, ↓reduceIte, FirstOrder.denote,
            ih vs v s left p hp, ih vs v s right q hq]
    | implies actual left right =>
        simp only [Checking.elaborate] at accepted
        split at accepted
        · contradiction
        · rename_i valid
          obtain ⟨p, hp, rest⟩ := Option.bind_eq_some_iff.mp accepted
          obtain ⟨q, hq, result⟩ := Option.bind_eq_some_iff.mp rest
          have eq := Option.some.inj result
          subst typed
          simp only [denote, valid, ↓reduceIte, FirstOrder.denote,
            ih vs v s left p hp, ih vs v s right q hq]
    | iff actual left right =>
        simp only [Checking.elaborate] at accepted
        split at accepted
        · contradiction
        · rename_i valid
          obtain ⟨p, hp, rest⟩ := Option.bind_eq_some_iff.mp accepted
          obtain ⟨q, hq, result⟩ := Option.bind_eq_some_iff.mp rest
          have eq := Option.some.inj result
          subst typed
          simp only [denote, valid, ↓reduceIte, FirstOrder.denote,
            ih vs v s left p hp, ih vs v s right q hq]
    | «exists» actual name b body =>
        simp only [Checking.elaborate] at accepted
        split at accepted
        · contradiction
        · rename_i valid
          obtain ⟨p, hp, result⟩ := Option.bind_eq_some_iff.mp accepted
          have eq := Option.some.inj result
          subst typed
          have bodyMeaning (x : M.carrier b) :
              denote M n (⟨name, b, {x}⟩ :: interpret M vs v) s body =
                FirstOrder.denote scope.signature M (Γ := Fin.cases b Γ) (Fin.cases x v) p := by
            simpa only [interpret_bind] using
              ih (Γ := Fin.cases b Γ) (Checking.bind name b vs) (Fin.cases x v) s body p hp
          simp only [denote, valid, Bool.false_eq_true, ↓reduceIte, FirstOrder.denote, bodyMeaning]
    | «forall» actual name b body =>
        simp only [Checking.elaborate] at accepted
        split at accepted
        · contradiction
        · rename_i valid
          obtain ⟨p, hp, result⟩ := Option.bind_eq_some_iff.mp accepted
          have eq := Option.some.inj result
          subst typed
          have bodyMeaning (x : M.carrier b) :
              denote M n (⟨name, b, {x}⟩ :: interpret M vs v) s body =
                FirstOrder.denote scope.signature M (Γ := Fin.cases b Γ) (Fin.cases x v) p := by
            simpa only [interpret_bind] using
              ih (Γ := Fin.cases b Γ) (Checking.bind name b vs) (Fin.cases x v) s body p hp
          simp only [denote, valid, Bool.false_eq_true, ↓reduceIte, FirstOrder.denote, bodyMeaning]
    | app name args =>
        simp only [Checking.elaborate] at accepted
        cases symbolLookup : scope.symbols.attach.find? (fun d => d.val.declaration.name == name) with
        | some d =>
            simp only [symbolLookup] at accepted
            split at accepted
            · rename_i outputSort
              split at accepted
              · rename_i arity
                obtain ⟨ps, hps, result⟩ := Option.bind_eq_some_iff.mp accepted
                have eq := Option.some.inj result
                subst typed
                have argumentMeaning (i : Fin d.val.declaration.arguments.length) :
                    denote M n (interpret M vs v) (d.val.declaration.arguments.get i)
                        (args.get ⟨i.val, by omega⟩) =
                      FirstOrder.denote scope.signature M v (ps i) :=
                  ih vs v _ _ _ (collect_some _ _ hps i)
                simp only [denote, symbolLookup, outputSort, arity, ↓reduceDIte,
                  FirstOrder.denote, argumentMeaning]
              · contradiction
            · contradiction
        | none =>
            simp only [symbolLookup] at accepted
            obtain ⟨a, aliasLookup, accepted⟩ := Option.bind_eq_some_iff.mp accepted
            split at accepted
            · contradiction
            · rename_i valid
              obtain ⟨ps, hps, bodyAccepted⟩ := Option.bind_eq_some_iff.mp accepted
              have argumentEnvironments : interpret M ps v =
                  (a.declaration.parameters.zip args).map (fun (formal, arg) =>
                    (⟨formal.1, formal.2, denote M n (interpret M vs v) formal.2 arg⟩ : Binding M)) := by
                apply mapM_interpret _ _ _ _ _ hps
                intro pair entry hentry
                rcases pair with ⟨formal, arg⟩
                obtain ⟨p, hp, result⟩ := Option.bind_eq_some_iff.mp hentry
                have eq := Option.some.inj result
                subst entry
                dsimp only
                rw [ih vs v formal.2 arg p hp]
              have bodyMeaning := ih ps v s a.declaration.body typed bodyAccepted
              simpa only [denote, symbolLookup, aliasLookup, valid, Bool.false_eq_true, ↓reduceIte,
                ← argumentEnvironments] using bodyMeaning
end Silmaril.Proofs.Logic.Kore.Modules.Semantics
