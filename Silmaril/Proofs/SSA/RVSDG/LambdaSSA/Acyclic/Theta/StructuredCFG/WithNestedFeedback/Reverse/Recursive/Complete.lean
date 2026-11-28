module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Recursive.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Reverse.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Structured.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Reverse.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Recursive.Proofs

open Sequential
open Sequential.Flat.Serial (Code)
open Sequential.Flat.Serial.Recognize (mark Output)
open Sequential.Flat.Numbered.Recognize
  (budget opcodeKey instructionKey effectKey parse_thetaBody loop_associated)
open NestedFeedback.Reverse (Key readTheta readOuterWith)
open NestedTheta (Node)
open NestedTheta.ExplicitRuntime (Checked EntryChecked thetaNode)
open NestedTheta.ExplicitRuntime.Splice (Routing relocate append changeLive)
open OrderedRuntime.Structured (Data Threaded runtime primitiveNode gammaNode)
open TwoBlock.TwoExit (Pure)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {args input outs : Ports (OrderedRuntime.Structured.Ty τ)}
variable {past sigs target after : List (Ports (OrderedRuntime.Structured.Ty τ))}

private theorem scan_relocate {a : Data input} {b : Data outs} {c : Data args}
    {live : Origin (Threaded input) past runtime}
    {t : NestedTheta.Term (Wires.Op Φ) (Threaded input) past sigs (Threaded outs)}
    (route : Routing (Threaded input) past (Threaded args) target)
    (h : Checked (Pure τ) (Wires.Effect Φ) a b live t) :
    scan (relocate (c := c) route h).1 = scan t := by
  induction h generalizing args target with
  | ret => rfl
  | primitive live i o op wires rest ih =>
    simp only [relocate, scan, ih, Node.ofBase, primitiveNode]
  | gamma extra selector live i o xs sigs arms rest ihArms ihRest =>
    simp only [relocate, scan, ihRest, Node.ofBase, gammaNode]
  | theta live i wires sigs body rest ihBody ihRest =>
    simp only [relocate, scan, ihRest, thetaNode]

private theorem cons_append (head : Option (Entry τ Φ)) (rest tail : Option (Layout τ Φ)) :
    (do let h ← head; let suffix ← (do let xs ← rest; let ys ← tail; pure (xs ++ ys)); pure (h :: suffix)) =
      (do let xs ← (do let h ← head; pure (h :: (← rest))); let ys ← tail; pure (xs ++ ys)) := by
  cases head <;> cases rest <;> cases tail <;> rfl

theorem scan_append {a : Data args} {b : Data input} {c : Data outs}
    {live : Origin (Threaded args) past runtime}
    {p : NestedTheta.Term (Wires.Op Φ) (Threaded args) past sigs (Threaded input)}
    {q : NestedTheta.Term (Wires.Op Φ) (Threaded input) [] after (Threaded outs)}
    (first : Checked (Pure τ) (Wires.Effect Φ) a b live p) (next : EntryChecked (a := b) (b := c) q) :
    scan (append next first).1 = (do let xs ← scan p; let ys ← scan q; pure (xs ++ ys)) := by
  induction first with
  | ret =>
    simp only [append, scan_relocate, scan]
    cases scan q <;> rfl
  | primitive live i o op wires rest ih =>
    simp only [append, scan, Node.ofBase, primitiveNode, ih]
    exact cons_append _ _ _
  | gamma extra selector live i o xs sigs arms rest ihArms ihRest =>
    simp only [append, scan, Node.ofBase, gammaNode, ihRest]
    exact cons_append _ _ _
  | theta live i wires sigs body rest ihBody ihRest =>
    simp only [append, scan, thetaNode, ihRest]
    exact cons_append _ _ _

variable {A B K X Z M Y I J U V L E D : τ}
variable {ps qs ts : List (Ports (OrderedRuntime.Structured.Ty τ))}

private def loopEntry (s : Loop Φ A B K E D) : Entry τ Φ :=
  let body := ExplicitRuntime.Wiring.thetaBody s
  .atom (.loop (budget (Wires.liftChecked body.2.2).1) [.theta (ExplicitRuntime.Reverse.read body.2.1)])

private def cutEntry (h m i j : τ) : Entry τ Φ := .atom (.cut h m i j)

private def keys (s : NestedFeedback.Loop Φ A B K M) : Key τ Φ × Key τ Φ × Key τ Φ :=
  (.enter A B K M s.enter.op, .inner B K s.inner.op, .finish A B K M s.finish.op)

private def emitLeaf : {A X Z : τ} → {ps : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    LeafView Φ A X Z ps → Layout τ Φ
  | _, _, _, _, .localLoop s => [loopEntry s]
  | a, m, _, _, .feedback s => [.enter a m, .feedback (keys s), .leave a m]

private def emitted : {A X Z L E D : τ} → {ps : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    Normal Φ A X Z L E D ps → Layout τ Φ
  | _, _, _, _, _, _, _, .leaf p => emitLeaf p
  | a, m, _, _, _, _, _, .seq (I := i) (J := j) p k => emitLeaf p ++ cutEntry a m i j :: emitted k
  | _, _, _, _, _, _, _, .fork (U := u) (V := v) (M := m) (Y := y) (I := i) (J := j) gate p q k =>
    .classifier gate ::
      .fork (cutEntry y m m m :: (emitted p ++ [cutEntry u m i j]))
        (emitted q ++ [cutEntry v m i j]) :: emitted k

private theorem scan_leaf (p : LeafView Φ A X Z ps) : scan p.toSyntax.code.1 = some (emitLeaf p) := by
  cases p with
  | localLoop s =>
    simp only [LeafView.toSyntax, Syntax.code, StructuredCFG.Syntax.code, Flat.Serial.Spine.code,
      ExplicitRuntime.Wiring.loop, Wires.liftChecked, scan, readEntry, mark, thetaNode,
      Wires.Reverse.readBody_lift, emitLeaf, loopEntry]
    rfl
  | feedback s =>
    simp only [LeafView.toSyntax, Syntax.code, Leaf.code, Leaf.bridge, Leaf.liftChecked,
      NestedFeedback.Wiring.loop, append, relocate, changeLive, Node.ofBase, primitiveNode, thetaNode,
      Leaf.Sigs, List.cons_append, List.nil_append, scan, readEntry, readOpcode, opcodeKey,
      instructionKey, effectKey, Option.bind_some, readTheta, readOuterWith, readNested,
      Leaf.liftInstruction, NestedFeedback.Wiring.outerBody, NestedFeedback.Wiring.innerBody,
      NestedFeedback.Wiring.returnStep, NestedFeedback.Reverse.effectKey, NestedFeedback.Reverse.readInnerWith,
      emitLeaf, keys]
    rfl

private theorem scan_cut :
    scan (Flat.Numbered.connector (Φ := Φ) (I := U) (M := M) (E := I) (D := J)).1 =
      some [cutEntry U M I J] := rfl

private theorem scan_select (gate : TwoBlock.Instruction Φ A (ChoiceCarrier M Y))
    (p : Code Φ M M M U M M ps) (q : Code Φ Y M M V M M qs) (left right : Layout τ Φ)
    (hp : scan p.1 = some left) (hq : scan q.1 = some right) :
    scan (StructuredCFG.Wiring.select (X := X) (Z := Z) (I := I) (J := J) gate p q).1 =
      some [.classifier gate, .fork
        (cutEntry Y M M M :: (left ++ [cutEntry U M I J])) (right ++ [cutEntry V M I J])] := by
  simp only [StructuredCFG.Wiring.select, scan, Node.ofBase, primitiveNode, gammaNode, readEntry,
    readOpcode, opcodeKey, instructionKey, effectKey,
    Wires.Reverse.readKind, ExplicitRuntime.Reverse.primitive, Fin.cases_zero]
  change (do
    let classifier ← some (Entry.classifier gate)
    let body ← (do
      let fork ← (do
        return Entry.fork (← scan (StructuredCFG.Wiring.leftArm (I := I) (J := J) p).1)
          (← scan (StructuredCFG.Wiring.rightArm (I := I) (J := J) q).1))
      let rest ← some []
      return fork :: rest)
    return classifier :: body) = _
  simp only [StructuredCFG.Wiring.leftArm, StructuredCFG.Wiring.rightArm, scan_append, scan_cut, hp, hq]
  rfl

private theorem scan_emitted (n : Normal Φ A X Z L E D ps) : scan n.toSyntax.code.1 = some (emitted n) := by
  induction n with
  | leaf p => exact scan_leaf p
  | seq p k ih =>
    simp only [Normal.toSyntax, Syntax.code, Flat.Serial.splice, scan_append, scan_leaf,
      scan_cut, ih, emitted]
    rfl
  | fork gate p q k hp hq hk =>
    simp only [Normal.toSyntax, Syntax.code, StructuredCFG.Wiring.branch, scan_append, hk,
      scan_select gate _ _ _ _ hp hq, emitted]
    rfl

theorem weight_append (p q : Layout τ Φ) : weight (p ++ q) = weight p + weight q := by
  induction p with
  | nil => simp [weight]
  | cons head tail ih =>
    cases head <;> simp only [List.cons_append, weight, ih] <;> omega

private theorem weight_leaf (p : LeafView Φ A X Z ps) : 0 < weight (emitLeaf p) := by
  cases p <;> simp [emitLeaf, loopEntry, weight]

variable [DecidableEq τ] in
private theorem split_snoc (p : Layout τ Φ) (h m i j : τ) :
    splitArm (p ++ [.atom (.cut h m i j)]) m = some (⟨h,i,j⟩, p) := by
  simp [splitArm, List.reverse_append]

private theorem associate_leaf (p : LeafView Φ A X Z ps) :
    ∃ q : LeafView Φ A X Z ps, q.Supported ∧ q.toSyntax.code = p.toSyntax.code := by
  cases p with
  | localLoop s =>
    obtain ⟨t, ht, same⟩ := loop_associated s
    refine ⟨.localLoop t, ht, ?_⟩
    change Wires.liftChecked (ExplicitRuntime.Wiring.loop t).2 =
      Wires.liftChecked (ExplicitRuntime.Wiring.loop s).2
    rw [same]
  | feedback s => exact ⟨.feedback s, trivial, rfl⟩

private theorem associate_bodies (n : Normal Φ A X Z L E D ps) :
    ∃ out : Normal Φ A X Z L E D ps, out.Supported ∧ out.toSyntax.code = n.toSyntax.code := by
  induction n with
  | leaf p =>
    obtain ⟨q, hq, same⟩ := associate_leaf p
    exact ⟨.leaf q, hq, same⟩
  | seq p k ih =>
    obtain ⟨q, hq, same⟩ := associate_leaf p
    obtain ⟨tail, ht, code⟩ := ih
    refine ⟨.seq q tail, ⟨hq,ht⟩, ?_⟩
    simp only [Normal.toSyntax, Syntax.code, same, code]
  | fork gate p q k hp hq hk =>
    obtain ⟨left, hl, lc⟩ := hp
    obtain ⟨right, hr, rc⟩ := hq
    obtain ⟨tail, ht, tc⟩ := hk
    refine ⟨.fork gate left right tail, ⟨hl,hr,ht⟩, ?_⟩
    simp only [Normal.toSyntax, Syntax.code, lc, rc, tc]

variable [DecidableEq τ]

private theorem readLeaf_emitted (p : LeafView Φ A X Z ps) (h : p.Supported) (tail : Layout τ Φ) :
    readLeaf A X Z (emitLeaf p ++ tail) = some (⟨ps,p⟩, tail) := by
  cases p with
  | localLoop s =>
    simp [emitLeaf, loopEntry, readLeaf, parse_thetaBody s h]
  | feedback s =>
    simp [emitLeaf, readLeaf, keys, NestedFeedback.Reverse.decode_generated]

private theorem parse_emitted (n : Normal Φ A X Z L E D ps) (h : n.Supported)
    (fuel : Nat) (enough : weight (emitted n) ≤ fuel) :
    parse fuel A X Z (emitted n) = some (pack n) := by
  induction n generalizing fuel with
  | leaf p =>
    cases fuel with
    | zero =>
      have positive := weight_leaf p
      simp only [emitted] at enough
      omega
    | succ fuel =>
      have parsed := readLeaf_emitted p h []
      cases p <;> simp only [emitted, emitLeaf, loopEntry, parse, List.append_nil] at parsed ⊢ <;> simp [parsed]
  | @seq a m i j l e d ps qs p k ih =>
    obtain ⟨head, tail⟩ := h
    cases fuel with
    | zero =>
      have positive := weight_leaf p
      simp only [emitted, weight_append] at enough
      omega
    | succ fuel =>
      simp only [emitted, cutEntry, weight_append, weight] at enough
      have bounded : weight (emitted k) ≤ fuel := by omega
      have parsed := readLeaf_emitted p head (cutEntry a m i j :: emitted k)
      cases p <;> simp only [emitted, emitLeaf, loopEntry, cutEntry, List.cons_append, List.nil_append, parse] at parsed ⊢ <;>
        simp [parsed, ih tail fuel bounded, pack]
  | fork gate p q k hp hq hk =>
    obtain ⟨left, right, tail⟩ := h
    cases fuel with
    | zero => simp [emitted, weight] at enough
    | succ fuel =>
      simp only [emitted, cutEntry, weight, weight_append] at enough
      have lp : weight (emitted p) ≤ fuel := by omega
      have rq : weight (emitted q) ≤ fuel := by omega
      have tk : weight (emitted k) ≤ fuel := by omega
      simp [emitted, parse, cutEntry, split_snoc, hp left fuel lp,
        hq right fuel rq, hk tail fuel tk, expect, pack]

omit [DecidableEq τ] in
private theorem route_not_mem_emitted (n : Normal Φ A X Z L E D ps) (h e m d : τ) :
    Entry.route h e m d ∉ emitted n := by
  induction n with
  | leaf p => cases p <;> simp [emitted, emitLeaf, loopEntry]
  | seq p k ih => cases p <;> simp [emitted, emitLeaf, loopEntry, cutEntry, ih]
  | fork gate p q k hp hq hk => simp [emitted, hk]

omit [DecidableEq τ] in
theorem scan_route_free (n : Normal Φ A X Z L E D ps) {labels : Layout τ Φ}
    (scanned : scan n.toSyntax.code.1 = some labels) (h e m d : τ) :
    Entry.route h e m d ∉ labels := by
  rw [scan_emitted] at scanned
  cases scanned
  exact route_not_mem_emitted n h e m d

theorem scan_parse_generated (n : Normal Φ A X Z L E D ps) (h : n.Supported) :
    ∃ labels, scan n.toSyntax.code.1 = some labels ∧
      parse (weight labels) A X Z labels = some (pack n) :=
  ⟨emitted n, scan_emitted n, parse_emitted n h _ (Nat.le_refl _)⟩

theorem candidate_generated (n : Normal Φ A X Z L E D ps) (h : n.Supported) :
    candidate n.toSyntax.graph = some n := by
  simp only [candidate, decodeLayout, Syntax.graph, NestedTheta.Term.toTerm_toGraph, scan_emitted]
  have parsed := parse_emitted n h (weight (emitted n)) (Nat.le_refl _)
  change (do
    let ⟨out, shape⟩ ← parse (weight (emitted n)) A X Z (emitted n)
    if eq : out = (⟨L,E,D,ps⟩ : Output τ) then
      some (Eq.mp (congrArg (fun ix => Normal Φ A X Z ix.carry ix.left ix.right ix.sigs) eq) shape)
    else none) = some n
  rw [parsed]
  simp [pack]

variable [DecidableEq Φ]

theorem recover_generated (n : Normal Φ A X Z L E D ps) (h : n.Supported) :
    recover n.toSyntax.graph = some ⟨n.toSyntax.source.region, .generated n.toSyntax⟩ := by
  simp [recover, recognize, candidate_generated n h, certify, Decomposition.raise]

theorem recover_isSome_iff (g : Flat.Serial.Graph Φ A X Z L E D ps) :
    (recover g).isSome = true ↔ ∃ n : Normal Φ A X Z L E D ps, n.toSyntax.graph = g := by
  constructor
  · intro accepted
    cases h : candidate g with
    | none => simp [recover, recognize, h] at accepted
    | some n =>
      use n
      by_contra different
      simp [recover, recognize, h, certify, different] at accepted
  · rintro ⟨n, rfl⟩
    obtain ⟨out, supported, code⟩ := associate_bodies n
    have same : out.toSyntax.graph = n.toSyntax.graph := congrArg (fun c => c.1.toGraph) code
    rw [← same, recover_generated out supported]
    rfl

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Recursive.Proofs
