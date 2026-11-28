module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded

open Silmaril.Isotope Silmaril.Isotope.Bridge.NamedFlat Silmaril.Isotope.Bridge.NamedFlat.Entry
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded
open Silmaril.Elgot (iter mapReturn liftPure)
open Silmaril.Elgot.ITree (Tree iterate_uniformity iterate_naturality)
open Silmaril.SSA.LambdaRTL (CFG obs)
open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics.Interaction (Primitive Transfer)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LambdaSSA.UB.Overlay.Shape
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands (Head Table productContains productContains_iff ReplyEnumeration)

section Named

variable {κ V K α : Type 1} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{0, 0} κ} [HasTy P.Instr Syntax.Ty]
  {I : Interface κ V K} {fields : K → List (V × Ty κ)} {source : CFG V K P.Instr}
  {N : RequestSignature P.Instr} {R : List Syntax.Ty} {E : Type → Type}
  {a : Admission P I fields source} {g : Table N R} {caller : Syntax.Payload (R.get g.entry)}
  {result : TwoRequest.Tag → Transfer α} {query : Query N E} {instr : Primitive E P.Instr α} {input : V × Nat → Value α}

theorem mutable_step (c : Corresponds a g caller query instr input result) (state : Cursor R)
    (pending : CFG.Cyclic.Transfer V K (Value α))
    (encoded : c.encode state =
      let m := treeModel instr
      let selected := fun k => (fields k).map Prod.fst
      CFG.Cyclic.Versioning.encodePacketLocal m (CFG.Cyclic.LiveOut.attach selected source)
        (CFG.Cyclic.LiveOut.encode m selected source pending)) :
    let m := treeModel instr
    let selected := fun k => (fields k).map Prod.fst
    let outgoing := fun p => FiniteCFG.packedTreeOutput
      (treeExitNumber I.exits (obs (CFG.Cyclic.LiveOut.project m selected p)))
    let again := fun p => CFG.Cyclic.Versioning.encodePacketLocal m (CFG.Cyclic.LiveOut.attach selected source)
      (CFG.Cyclic.LiveOut.encode m selected source p)
    (step g caller query result state >>= liftPure (Sum.map id c.encode)) =
      Sum.map outgoing again <$> CFG.Cyclic.step m source.blocks pending := by
  let m := treeModel instr
  let selected := fun k => (fields k).map Prod.fst
  let attached := CFG.Cyclic.LiveOut.attach selected source
  let project := CFG.Cyclic.LiveOut.project m selected
  let attach := CFG.Cyclic.LiveOut.encode m selected source
  let encode := CFG.Cyclic.Versioning.encodePacketLocal m attached
  let number := fun (p : K × Value α) => FiniteCFG.packedTreeOutput (treeExitNumber I.exits p)
  let s := CFG.Cyclic.step m source.blocks pending
  change _ = Sum.map (number ∘ obs ∘ project) (encode ∘ attach) <$> s
  have lexical := CFG.Cyclic.Versioning.stepPacketLocal_commutes m ⟨fun _ _ => rfl⟩ attached
    a.closed input (attach pending)
  have mutable := CFG.Cyclic.LiveOut.step_commutes m selected source pending
  rw [c.localStep state, a.compiled, encoded]
  change ((CFG.Cyclic.stepSSA m (CFG.Cyclic.Versioning.compilePacketLocal attached).blocks input
    (encode (attach pending))) >>= _) = _
  rw [← lexical, ← mutable]
  simp only [map_eq_pure_bind, bind_assoc, pure_bind]
  congr 1
  funext out
  cases out with
  | inl p =>
    change (pure (number (obs (project p))) >>= _) = _
    rw [pure_bind]
    rfl
  | inr => rfl

omit [HasTy P.Instr Syntax.Ty] in
theorem observe_eq_of_steps {C : Type 1}
    (start : C) (next : C → Tree E (Transfer α ⊕ C)) (encode : C → K × Value α)
    (entry : a.versioned.source.entry.evalJump (treeModel instr) input = pure (encode start))
    (localStep : ∀ c,
      (next c >>= liftPure (Sum.map id encode)) =
        mapReturn (CFG.Cyclic.stepSSA (treeModel instr) a.versioned.source.blocks input)
          (liftPure fun p => FiniteCFG.packedTreeOutput (treeExitNumber I.exits p)) (encode c)) :
    LiveOut.observeRaw instr I.exits (fun k => (fields k).map Prod.fst) source
      (fun reg => input (reg, 0)) = iter next start := by
  let m := treeModel instr
  let number := fun (p : K × Value α) => FiniteCFG.packedTreeOutput (treeExitNumber I.exits p)
  let lexicalStep := CFG.Cyclic.stepSSA m a.versioned.source.blocks input
  let actual := mapReturn lexicalStep (liftPure number)
  have same := congrFun (iterate_uniformity next actual encode
    (funext fun i => by
      change (next i >>= liftPure (Sum.map id encode)) =
        (pure (encode i) >>= actual)
      rw [pure_bind]
      exact localStep i)) start
  change iter next start = (pure (encode start) >>= iter actual) at same
  rw [pure_bind] at same
  have versioned := CFG.Cyclic.Versioning.runPacketLocal_commutes m ⟨fun _ _ => rfl⟩
    (CFG.Cyclic.LiveOut.attach (fun k => (fields k).map Prod.fst) source) a.closed input
  calc
    _ = (CFG.Cyclic.runSSA m a.versioned.source input >>= liftPure number) := by
      rw [a.compiled, ← versioned, CFG.Cyclic.LiveOut.run_project]
      simp only [LiveOut.observeRaw, bind_map_left]
      rfl
    _ = iter lexicalStep (encode start) >>= liftPure number := by
      simp only [CFG.Cyclic.runSSA, entry, pure_bind, lexicalStep, m]
    _ = iter actual (encode start) :=
      congrFun (iterate_naturality lexicalStep (liftPure number)) _
    _ = _ := same.symm

theorem observe_eq (c : Corresponds a g caller query instr input result) :
    LiveOut.observeRaw instr I.exits (fun k => (fields k).map Prod.fst) source
      (fun reg => input (reg, 0)) =
      iter (step g caller query result) (atBlock ⟨g.entry, caller⟩) :=
  observe_eq_of_steps _ _ c.encode c.entry c.localStep

end Named

section Product

variable {Φ : Type} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ}
  {R T : List Syntax.Ty} {E : Type → Type} {B : Type 1}

private inductive Coupled (rel : Packet R → Packet T → Prop) : Type 1
  | exit (i : TwoRequest.Tag)
  | block (p : Packet R) (q : Packet T) (related : rel p q)

private def Coupled.left {rel : Packet R → Packet T → Prop} : Coupled rel → Cursor R
  | .exit i => atExit i
  | .block p _ _ => atBlock p

private def Coupled.right {rel : Packet R → Packet T → Prop} : Coupled rel → Cursor T
  | .exit i => atExit i
  | .block _ q _ => atBlock q

private theorem pairedHeads (query : Query S E) (rel : Packet R → Packet T → Prop)
    (p : Head S R) (q : Head S T) (matched : p.Matches rel q)
    (ordinary : ∀ i, q ≠ .exit i true) :
    ∃ next : Tree E (B ⊕ Coupled rel),
      (next >>= liftPure (Sum.map id Coupled.left)) = headStep query p ∧
      (next >>= liftPure (Sum.map id Coupled.right)) = headStep query q := by
  cases q with
  | exit j marked =>
    cases marked
    · cases p with
      | exit i mark =>
        cases mark
        · change i = j at matched
          subst j
          exact ⟨pure (.inr (.exit i)), by simp [liftPure, Coupled.left, headStep],
            by simp [liftPure, Coupled.right, headStep]⟩
        · contradiction
      | request | diverge => contradiction
    · exact (ordinary j rfl).elim
  | diverge =>
    cases p with
    | exit | request => contradiction
    | diverge => exact ⟨Silmaril.Elgot.ITree.diverge, by simp [headStep], by simp [headStep]⟩
  | request op arg next =>
    cases p with
    | exit | diverge => contradiction
    | request op' arg' next' =>
      obtain ⟨key, args, matchesReply⟩ := matched
      subst op'
      have same : arg' = arg := Subtype.ext args
      subst arg'
      refine ⟨query op arg >>= fun r => pure (.inr (.block
        (next' r.down.1 r.down.2) (next r.down.1 r.down.2) (matchesReply r.down))), ?_, ?_⟩
      · simp [headStep, liftPure, Coupled.left]
      · simp [headStep, liftPure, Coupled.right]

private theorem head_ordinary (h : Table S T) (caller : Syntax.Payload (T.get h.entry))
    (q : Packet T) (ordinary : ∀ i, h.selected i = false) :
    ∀ i, h.head caller q ≠ .exit i true := by
  intro i same
  unfold Table.head at same
  split at same
  · simp [ordinary] at same
  · contradiction
  · contradiction

theorem iter_eq_of_closed (g : Table S R) (h : Table S T)
    (caller : Syntax.Payload (R.get g.entry)) (caller' : Syntax.Payload (T.get h.entry))
    (query : Query S E) (result : TwoRequest.Tag → B) (rel : Packet R → Packet T → Prop)
    (closed : ∀ p q, rel p q → (g.head caller p).Matches rel (h.head caller' q))
    (ordinary : ∀ i, h.selected i = false)
    {p : Packet R} {q : Packet T} (related : rel p q) :
    iter (step g caller query result) (atBlock p) =
      iter (step h caller' query result) (atBlock q) := by
  have extend (c : Coupled rel) : ∃ next : Tree E (B ⊕ Coupled rel),
      (next >>= liftPure (Sum.map id Coupled.left)) = step g caller query result c.left ∧
      (next >>= liftPure (Sum.map id Coupled.right)) = step h caller' query result c.right := by
    cases c with
    | exit i =>
      exact ⟨pure (.inl (result i)), by simp [step, liftPure, Coupled.left, atExit],
        by simp [step, liftPure, Coupled.right, atExit]⟩
    | block p q related =>
      exact pairedHeads query rel _ _ (closed p q related) (head_ordinary h caller' q ordinary)
  let coupled := fun c => Classical.choose (extend c)
  let entry := Coupled.block p q related
  have left := congrFun (iterate_uniformity coupled (step g caller query result) Coupled.left
    (funext fun c => by
      change (coupled c >>= liftPure (Sum.map id Coupled.left)) = (pure c.left >>= step g caller query result)
      rw [pure_bind]
      exact (Classical.choose_spec (extend c)).1)) entry
  change iter coupled entry = (pure (atBlock p) >>= iter (step g caller query result)) at left
  rw [pure_bind] at left
  have right := congrFun (iterate_uniformity coupled (step h caller' query result) Coupled.right
    (funext fun c => by
      change (coupled c >>= liftPure (Sum.map id Coupled.right)) = (pure c.right >>= step h caller' query result)
      rw [pure_bind]
      exact (Classical.choose_spec (extend c)).2)) entry
  change iter coupled entry = (pure (atBlock q) >>= iter (step h caller' query result)) at right
  rw [pure_bind] at right
  exact left.symm.trans right

theorem iter_eq_of_checkProduct [DecidableEq Φ] (g : Table S R) (h : Table S T)
    (caller : Syntax.Payload (R.get g.entry)) (caller' : Syntax.Payload (T.get h.entry))
    (query : Query S E) (result : TwoRequest.Tag → B)
    (replies : ReplyEnumeration S) (pairs : List (Packet R × Packet T))
    (checked : g.checkProduct h caller caller' replies pairs = true)
    (ordinary : ∀ i, h.selected i = false) :
    iter (step g caller query result) (atBlock ⟨g.entry, caller⟩) =
      iter (step h caller' query result) (atBlock ⟨h.entry, caller'⟩) := by
  obtain ⟨entry, rows⟩ := Bool.and_eq_true_iff.mp checked
  apply iter_eq_of_closed g h caller caller' query result (fun p q => productContains pairs p q = true)
    _ ordinary entry
  intro p q related
  apply (Head.checkPair_iff replies (productContains pairs) _ _).mp
  exact List.all_eq_true.mp rows (p, q) ((productContains_iff pairs p q).mp related)

end Product

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded
