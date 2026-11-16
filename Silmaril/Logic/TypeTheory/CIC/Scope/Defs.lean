module

public import Silmaril.Logic.TypeTheory.CIC.Environment.Defs

@[expose] public section

/-! # Local scope of raw CIC terms

This is PCUIC's `closedn` convention: cached case contexts stay in declaration
scope. Named free placeholders are never locally closed.
-/

namespace Silmaril.Logic.TypeTheory.CIC.Term

universe u

/-- Check that all local de Bruijn indices are below the available binder count. -/
def isClosed {Level : Type u} (count : ℕ) : Term Level → Bool
  | .rel i => i < count
  | .free _ => false
  | .sort _ | .constant _ _ | .inductiveType _ _ | .constructor _ _ _ => true
  | .prod _ A B | .lam _ A B => isClosed count A && isClosed (count + 1) B
  | .letIn _ value A body =>
      isClosed count value && isClosed count A && isClosed (count + 1) body
  | .app f a => isClosed count f && isClosed count a
  | .caseOf _ p c branches =>
      p.parameters.attach.all (fun a => isClosed count a.val) &&
      isClosed (count + p.context.length) p.returnType && isClosed count c &&
      branches.attach.all (fun b => isClosed (count + b.val.context.length) b.val.body)
  | .projection _ c => isClosed count c
  | .fix definitions _ | .cofix definitions _ =>
      definitions.attach.all (fun d => isClosed count d.val.type &&
        isClosed (count + definitions.length) d.val.body)
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals
    first
    | have h := List.sizeOf_lt_of_mem a.property
      cases p
      simp_all only [Predicate.mk.sizeOf_spec]
      omega
    | have h := List.sizeOf_lt_of_mem b.property
      rcases b with ⟨b, hb⟩
      cases b
      cases p
      simp_all only [Predicate.mk.sizeOf_spec, Branch.mk.sizeOf_spec]
      omega
    | have h := List.sizeOf_lt_of_mem d.property
      rcases d with ⟨d, hd⟩
      cases d
      simp_all only [FixDef.mk.sizeOf_spec]
      omega
    | cases p
      simp only [Predicate.mk.sizeOf_spec]
      omega

end Silmaril.Logic.TypeTheory.CIC.Term
