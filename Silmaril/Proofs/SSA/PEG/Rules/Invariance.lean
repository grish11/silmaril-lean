module

public import Silmaril.Proofs.SSA.PEG.Rules.Local

public section

namespace Silmaril.SSA.PEG.Rules.Proofs

open RVSDG (Tuple)

universe u v x

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results ins : List (Ty Data)} {out : Ty Data} {n l : Nat}
variable {g : Graph P params results n l} {m : Interpretation.{u,v,x} P}
variable {values : g.Valuation m} {env : Tuple m.Value params}

theorem invariantAt_notTheta {loop : Fin l} {a : Fin n} (h : InvariantAt g loop a) :
    (g.node a).label.thetaLoop ≠ some loop := h a [] (.nil a)

theorem invariantAt_step {loop : Fin l} {a b : Fin n} {kind : EdgeKind (Fin l)}
    (h : InvariantAt g loop a) (edge : InvarianceEdge g loop a kind b) : InvariantAt g loop b :=
  fun c ks path => h c (kind :: ks) (.cons edge path)

theorem invariantAt_iff {loop : Fin l} {a : Fin n} : InvariantAt g loop a ↔
    ((g.node a).label.thetaLoop ≠ some loop ∧
      ∀ {b kind}, InvarianceEdge g loop a kind b → InvariantAt g loop b) := by
  refine ⟨fun h => ⟨invariantAt_notTheta h, fun edge => invariantAt_step h edge⟩, ?_⟩
  rintro ⟨here, children⟩ b ks path
  cases path with
  | nil => exact here
  | cons edge rest => exact children edge _ _ rest

theorem invariantAt_largest {loop : Fin l} (p : Fin n → Prop)
    (noTheta : ∀ a, p a → (g.node a).label.thetaLoop ≠ some loop)
    (closed : ∀ {a b kind}, InvarianceEdge g loop a kind b → p a → p b)
    {a : Fin n} (ha : p a) : InvariantAt g loop a :=
  fun b _ path => noTheta b (path.preserves (fun edge _ => closed edge) ha)

private theorem sample_eq {loop other : Fin l} {i j : Index l} (same : AgreeExcept loop i j)
    (k : Nat) (h : EdgeKind.sample other = .sample loop) : i.set other k = j.set other k := by
  injection h with eq
  subst other
  exact set_eq_of_agree same k

/-- Match the reads used by Figure 11. At a sample of the designated coordinate the
actual indices must coincide. All other reads may retain the difference. -/
private theorem interpret_agree {loop : Fin l} {i j : Index l}
    (label : Label P params (Fin l) ins out) (same : AgreeExcept loop i j)
    (noTheta : label.thetaLoop ≠ some loop)
    (read : ∀ s : Fin ins.length, Index l → Option (m.Value ins[s]))
    (read_eq : ∀ (s : Fin ins.length) (a b : Index l), (label.kind s).Changes i a →
      AgreeExcept loop a b → (label.kind s = .sample loop → a = b) → read s a = read s b) :
    label.interpret m env i (fun s k _ => read s k) =
      label.interpret m env j (fun s k _ => read s k) := by
  cases label with
  | param p => rfl
  | op op =>
    change (collect _ (fun s => read s i)).elim none (m.run op) =
      (collect _ (fun s => read s j)).elim none (m.run op)
    exact congrArg (fun args => args.elim none (m.run op))
      (congrArg (collect _) (funext fun s => read_eq s i j rfl same (by simp [Label.kind])))
  | phi =>
    change (read 0 i).elim none (fun flag => if flag.down then read 1 i else read 2 i) =
      (read 0 j).elim none (fun flag => if flag.down then read 1 j else read 2 j)
    rw [read_eq 0 i j rfl same (by simp [Label.kind]),
      read_eq 1 i j rfl same (by simp [Label.kind]), read_eq 2 i j rfl same (by simp [Label.kind])]
  | theta other =>
    have distinct : other ≠ loop := fun h => noTheta (congrArg some h)
    have count := same other distinct
    cases h : i other with
    | zero =>
      have h' : j other = 0 := count.symm.trans h
      rw [interpret_theta, interpret_theta, h, h']
      exact read_eq 0 i j ⟨h, rfl⟩ same (by simp [Label.kind])
    | succ k =>
      have h' : j other = k + 1 := count.symm.trans h
      rw [interpret_theta, interpret_theta, h, h']
      exact read_eq 1 (i.set other k) (j.set other k) ⟨k, h, rfl⟩ (set_congr same other k)
        (by simp [Label.kind])
  | eval other =>
    change (read 1 i).elim none (fun k => monotonize (fun a => read 0 (i.set other a)) k.down) =
      (read 1 j).elim none (fun k => monotonize (fun a => read 0 (j.set other a)) k.down)
    have samples : (fun a => read 0 (i.set other a)) = fun a => read 0 (j.set other a) :=
      funext fun k => read_eq 0 _ _ ⟨k, rfl⟩ (set_congr same other k) (sample_eq same k)
    rw [read_eq 1 i j rfl same (by simp [Label.kind]), samples]
  | pass other =>
    change (firstTrue (fun a => (read 0 (i.set other a)).map ULift.down)).map ULift.up =
      (firstTrue (fun a => (read 0 (j.set other a)).map ULift.down)).map ULift.up
    exact congrArg (fun stream => (firstTrue stream).map ULift.up) (funext fun k =>
      congrArg (Option.map ULift.down)
        (read_eq 0 _ _ ⟨k, rfl⟩ (set_congr same other k) (sample_eq same k)))

theorem invariant_sound (wf : WellFounded g.Demand) (solves : g.Solves m env values)
    {loop : Fin l} {r : Ref g.sort out} (guard : InvariantAt g loop r.id) :
    Invariant values loop r := by
  have invariant : ∀ q (j : Index l), InvariantAt g loop q.1 → AgreeExcept loop q.2 j →
      values q = values (q.1, j) := by
    intro q
    induction q using wf.induction with
    | h q ih =>
      intro j safe same
      rw [solves q, solves (q.1, j)]
      let node := g.node q.1
      let read (s : Fin node.inputs.length) (i : Index l) := readRef values (node.arg s) i
      change node.label.interpret m env q.2 (fun s i _ => read s i) =
        node.label.interpret m env j (fun s i _ => read s i)
      apply interpret_agree node.label same (invariantAt_notTheta safe) read
      intro s a b changes agrees cut
      by_cases sample : node.label.kind s = .sample loop
      · exact congrArg (read s) (cut sample)
      · have edge : g.Edge q.1 (node.label.kind s) (node.arg s).id := ⟨s, rfl, rfl⟩
        have smaller : g.Demand ((node.arg s).id, a) q := ⟨_, edge, changes⟩
        exact congrArg ((node.arg s).read m.carrier)
          (ih _ smaller b (invariantAt_step safe ⟨edge, sample⟩) agrees)
  intro i j same
  exact congrArg (r.read m.carrier) (invariant (r.id, i) j guard same)

end Silmaril.SSA.PEG.Rules.Proofs
