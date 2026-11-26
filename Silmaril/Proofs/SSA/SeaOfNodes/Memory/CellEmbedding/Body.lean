module

public import Silmaril.SSA.SeaOfNodes.Memory.CellEmbedding.Defs

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.CellEmbedding.Proofs

open RVSDG (Locals Origin Port Tuple)

set_option backward.isDefEq.respectTransparency false

variable {small large : Nat} {args : List ValueSort}

theorem extend_apply_image (e : Embedding small large) (frame : Heap large) (source : Heap small)
    (a : Address small) : extend e frame source (e a) = source a := by
  unfold extend
  split
  · rename_i b found
    have foundEq := List.find?_some (p := fun x => decide (e x = e a)) found
    exact congrArg source (e.injective (of_decide_eq_true foundEq))
  · rename_i missing
    exact (List.find?_eq_none.mp missing a (List.mem_finRange a) (by simp)).elim

theorem extend_apply_outside (e : Embedding small large) (frame : Heap large) (source : Heap small)
    (a : Address large) (outside : (¬ ∃ b, e b = a)) : extend e frame source a = frame a := by
  unfold extend
  split
  · rename_i b found
    have foundEq := List.find?_some (p := fun x => decide (e x = a)) found
    exact (outside ⟨b, of_decide_eq_true foundEq⟩).elim
  · rfl

theorem eq_extend_iff (e : Embedding small large) (frame final : Heap large) (source : Heap small) :
    final = extend e frame source ↔ restrict e final = source ∧ SameFrame e frame final := by
  constructor
  · rintro rfl
    exact ⟨funext (extend_apply_image e frame source), fun a outside => extend_apply_outside e frame source a outside⟩
  · rintro ⟨onImage, outside⟩
    funext a
    by_cases image : ∃ b, e b = a
    · obtain ⟨b, rfl⟩ := image
      exact (congrFun onImage b).trans (extend_apply_image e frame source b).symm
    · exact (outside a image).trans (extend_apply_outside e frame source a image).symm

theorem extend_restrict (e : Embedding small large) (heap : Heap large) :
    extend e heap (restrict e heap) = heap :=
  ((eq_extend_iff e heap heap (restrict e heap)).mpr ⟨rfl, fun _ _ => rfl⟩).symm

theorem result_injective (e : Embedding small large) (frame : Heap large) :
    Function.Injective (result e frame) := by
  intro a b equal
  refine Prod.ext ?_ ?_
  · exact congrArg (fun out : Word × Heap large => out.1) equal
  · funext cell
    simpa only [result, extend_apply_image] using congrArg (fun out : Word × Heap large => out.2 (e cell)) equal

theorem write_extend (e : Embedding small large) (frame : Heap large) (source : Heap small)
    (a : Address small) (word : Word) :
    (extend e frame source).write (e a) word = extend e frame (source.write a word) := by
  apply (eq_extend_iff e frame _ _).mpr
  constructor
  · funext b
    change Function.update (extend e frame source) (e a) word (e b) = Function.update source a word b
    rw [Function.update_apply_of_injective (β := fun _ : Address large => Word) _ e.injective]
    exact congrArg (fun heap : Heap small => Function.update heap a word b)
      (funext (extend_apply_image e frame source))
  · intro b outside
    have different : b ≠ e a := fun equal => outside ⟨a, equal.symm⟩
    exact (Function.update_of_ne different word _).trans (extend_apply_outside e frame source b outside)

theorem input_get (e : Embedding small large) (values : Tuple (Val small) args)
    {sort : ValueSort} (port : Port args sort) :
    (input e values).get port = value e sort (values.get port) := by
  induction port with
  | head => cases values with | cons _ _ => rfl
  | tail _ ih => cases values with | cons _ rest => exact ih rest

private def locals (e : Embedding small large) : {past : List (List ValueSort)} →
    Locals (Val small) past → Locals (Val large) past
  | [], _ => PUnit.unit
  | _ :: _, values => (input e values.1, locals e values.2)

private theorem locals_get (e : Embedding small large) {past : List (List ValueSort)}
    (values : Locals (Val small) past) (i : Fin past.length) :
    (locals e values).get i = input e (values.get i) := by
  induction past with
  | nil => exact i.elim0
  | cons _ _ ih => exact Fin.cases rfl (fun j => ih values.2 j) i

private theorem readValue_embed (e : Embedding small large) (inputs : Tuple (Val small) args)
    {past : List (List ValueSort)} (ls : Locals (Val small) past) {sort : ValueSort}
    (origin : Origin args past sort) :
    readValue origin (input e inputs) (locals e ls) = value e sort (readValue origin inputs ls) := by
  cases origin with
  | arg port => exact input_get e inputs port
  | output i port =>
    change ((locals e ls).get i).get port = _
    rw [locals_get, input_get]
    rfl

private theorem denote_body (e : Embedding small large) (frame : Heap large) (inputs : Tuple (Val small) args) :
    {past : List (List ValueSort)} → {version : Nat} → (body : Body args past version) →
    (ls : Locals (Val small) past) → (initial : Heap small) →
    body.denote (input e inputs) (locals e ls) (extend e frame initial) =
      result e frame (body.denote inputs ls initial)
  | _, _, .ret _ origin, ls, initial => by
    rw [Body.denote, Body.denote, readValue_embed]
    rfl
  | _, _, .load _ address rest, ls, initial => by
    rw [Body.denote, Body.denote, readValue_embed]
    change rest.denote _ (.cons (extend e frame initial (e (readValue address inputs ls))) .nil, locals e ls) _ = _
    rw [extend_apply_image]
    exact denote_body e frame inputs rest (.cons (initial.read (readValue address inputs ls)) .nil, ls) initial
  | _, _, .store _ address source rest, ls, initial => by
    rw [Body.denote, Body.denote, readValue_embed, readValue_embed]
    change rest.denote (input e inputs) (locals e ls)
      ((extend e frame initial).write (e (readValue address inputs ls)) (readValue source inputs ls)) = _
    rw [write_extend]
    exact denote_body e frame inputs rest ls _

theorem denote_graph (e : Embedding small large) (frame : Heap large) (graph : Memory.Graph args)
    (inputs : Tuple (Val small) args) (initial : Heap small) :
    graph.denote (input e inputs) (extend e frame initial) = result e frame (graph.denote inputs initial) :=
  denote_body e frame inputs graph PUnit.unit initial

variable {middle : Nat}

theorem input_trans (e : Embedding small middle) (f : Embedding middle large)
    (values : Tuple (Val small) args) :
    input (e.trans f) values = input f (input e values) := by
  induction values with
  | nil => rfl
  | @cons sort _ head tail ih =>
    cases sort <;> simp only [input, Tuple.map, value] at ih ⊢ <;> rw [ih] <;> rfl

theorem sameFrame_trans (e : Embedding small middle) (f : Embedding middle large)
    (initial final : Heap large) :
    SameFrame (e.trans f) initial final ↔
      SameFrame f initial final ∧ SameFrame e (restrict f initial) (restrict f final) := by
  constructor
  · intro frame
    refine ⟨fun a outside => frame a (fun ⟨b, equal⟩ => outside ⟨e b, equal⟩), ?_⟩
    intro a outside
    exact frame (f a) (fun ⟨b, equal⟩ => outside ⟨b, f.injective equal⟩)
  · rintro ⟨outer, inner⟩ a outside
    by_cases hit : ∃ b, f b = a
    · obtain ⟨b, rfl⟩ := hit
      exact inner b (fun ⟨c, equal⟩ => outside ⟨c, congrArg f equal⟩)
    · exact outer a hit

theorem extend_trans (e : Embedding small middle) (f : Embedding middle large)
    (inner : Heap middle) (outer : Heap large) (source : Heap small) :
    extend (e.trans f) (extend f outer inner) source = extend f outer (extend e inner source) := by
  symm
  apply (eq_extend_iff (e.trans f) (extend f outer inner) _ source).mpr
  constructor
  · funext a
    change extend f outer (extend e inner source) (f (e a)) = _
    rw [extend_apply_image, extend_apply_image]
  · apply (sameFrame_trans e f _ _).mpr
    constructor
    · intro a outside
      rw [extend_apply_outside f _ _ a outside, extend_apply_outside f _ _ a outside]
    · intro a outside
      change extend f outer (extend e inner source) (f a) = extend f outer inner (f a)
      rw [extend_apply_image, extend_apply_image, extend_apply_outside e _ _ a outside]

theorem restrict_extend_disjoint (e : Embedding small large) (f : Embedding middle large)
    (disjoint : DisjointImages e f) (frame : Heap large) (source : Heap small) :
    restrict f (extend e frame source) = restrict f frame := by
  funext b
  exact extend_apply_outside e frame source (f b) (fun ⟨a, equal⟩ => disjoint a b equal)

theorem extend_disjoint_spec (e : Embedding small large) (f : Embedding middle large)
    (disjoint : DisjointImages e f) (initial : Heap large) (left : Heap small) (right : Heap middle) :
    let final := extend f (extend e initial left) right
    restrict e final = left ∧ restrict f final = right ∧
      (∀ a, (¬ ∃ b, e b = a) → (¬ ∃ b, f b = a) → final a = initial a) := by
  have leftSpec := (eq_extend_iff e initial (extend e initial left) left).mp rfl
  have rightSpec := (eq_extend_iff f (extend e initial left) (extend f (extend e initial left) right) right).mp rfl
  refine ⟨(restrict_extend_disjoint f e (fun b a equal => disjoint a b equal.symm) _ _).trans leftSpec.1,
    rightSpec.1, fun a outsideLeft outsideRight => ?_⟩
  exact (rightSpec.2 a outsideRight).trans (leftSpec.2 a outsideLeft)

end Silmaril.SSA.SeaOfNodes.Memory.CellEmbedding.Proofs
