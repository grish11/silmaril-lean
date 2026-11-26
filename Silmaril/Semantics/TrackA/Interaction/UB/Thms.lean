module

public import Silmaril.Semantics.TrackA.Interaction.UB.Defs
import Silmaril.Proofs.Semantics.TrackA.Interaction.UB.Laws

public section

namespace Silmaril.Semantics.TrackA.Interaction.UB

universe u v w

variable {T : Type u} {U : Type v} {V : Type w}

theorem collapse_gc (T : Type u) :
    GaloisConnection (collapse : Explicit T → Catastrophic T) Subtype.val :=
  (insertion T).gc

theorem collapse_val (s : Catastrophic T) : collapse s.val = s := (insertion T).l_u_eq s

theorem collapse_le_collapse_iff (s t : Explicit T) :
    collapse s ≤ collapse t ↔ none ∈ t ∨ s ⊆ t :=
  Proofs.Semantics.TrackA.Interaction.UB.collapse_le_collapse_iff s t

theorem val_collapse_of_safe (s : Explicit T) (h : none ∉ s) : (collapse s).val = s :=
  Proofs.Semantics.TrackA.Interaction.UB.val_collapse_of_safe s h

/-- Collapse preserves joins of arbitrary families, including the empty join. -/
theorem collapse_sSup (s : Set (Explicit T)) : collapse (sSup s) = sSup (collapse '' s) :=
  (collapse_gc T).l_sSup_eq_sSup_image

theorem collapse_eq_top_iff (s : Explicit T) : collapse s = ⊤ ↔ none ∈ s :=
  Proofs.Semantics.TrackA.Interaction.UB.collapse_eq_top_iff s

theorem collapse_inf_of_same_marker (s t : Explicit T) (marker : none ∈ s ↔ none ∈ t) :
    collapse (s ⊓ t) = collapse s ⊓ collapse t :=
  Proofs.Semantics.TrackA.Interaction.UB.collapse_inf_of_same_marker s t marker

/-- With an ordinary observation, collapse need not preserve a binary meet. -/
theorem collapse_inf_counterexample (t : T) :
    collapse ({none} ⊓ {some t} : Explicit T) ≠ collapse {none} ⊓ collapse {some t} :=
  Proofs.Semantics.TrackA.Interaction.UB.collapse_inf_counterexample t

@[simp] theorem val_bot : (⊥ : Catastrophic T).val = ∅ :=
  Proofs.Semantics.TrackA.Interaction.UB.val_bot

theorem nonempty_iff_ne_bot (x : Catastrophic T) : x.val.Nonempty ↔ x ≠ ⊥ :=
  Proofs.Semantics.TrackA.Interaction.UB.nonempty_iff_ne_bot x

theorem addBottom_le_iff (a b : WithBot (Nonempty T)) :
    addBottom a ≤ addBottom b ↔ a ≤ b :=
  Proofs.Semantics.TrackA.Interaction.UB.addBottom_le_iff a b

theorem addBottom_surjective : Function.Surjective (addBottom (T := T)) :=
  Proofs.Semantics.TrackA.Interaction.UB.addBottom_surjective

/-- Adding a new bottom to the nonempty fragment recovers the complete lattice. -/
noncomputable def bottomExtension (T : Type u) : WithBot (Nonempty T) ≃o Catastrophic T :=
  RelIso.ofSurjective
    ⟨⟨addBottom, fun _ _ h => le_antisymm ((addBottom_le_iff _ _).mp h.le)
      ((addBottom_le_iff _ _).mp h.ge)⟩, addBottom_le_iff _ _⟩ addBottom_surjective

theorem nonempty_sSup (s : Set (Catastrophic T)) (hs : s.Nonempty)
    (all : ∀ x ∈ s, x.val.Nonempty) : (sSup s).val.Nonempty :=
  Proofs.Semantics.TrackA.Interaction.UB.nonempty_sSup s hs all

namespace Nonempty

theorem no_common_lower_bound {x y : T} (different : x ≠ y) :
    ¬ ∃ b : Nonempty T, b ≤ pure x ∧ b ≤ pure y :=
  Proofs.Semantics.TrackA.Interaction.UB.no_common_lower_bound different

theorem pure_le_all [Subsingleton T] (t : T) (b : Nonempty T) : pure t ≤ b :=
  Proofs.Semantics.TrackA.Interaction.UB.pure_le_all t b

end Nonempty

theorem bind_mono {a b : Catastrophic T} {f g : T → Catastrophic U}
    (h : a ≤ b) (k : ∀ t, f t ≤ g t) : bind a f ≤ bind b g :=
  Proofs.Semantics.TrackA.Interaction.UB.bind_mono h k

theorem bind_assoc (s : Catastrophic T) (f : T → Catastrophic U) (g : U → Catastrophic V) :
    bind (bind s f) g = bind s (fun t => bind (f t) g) :=
  Proofs.Semantics.TrackA.Interaction.UB.bind_assoc s f g

@[simp] theorem pure_bind (t : T) (f : T → Catastrophic U) : bind (pure t) f = f t :=
  Proofs.Semantics.TrackA.Interaction.UB.pure_bind t f

@[simp] theorem bind_pure (s : Catastrophic T) : bind s pure = s :=
  Proofs.Semantics.TrackA.Interaction.UB.bind_pure s

@[simp] theorem top_bind (f : T → Catastrophic U) : bind ⊤ f = ⊤ :=
  Proofs.Semantics.TrackA.Interaction.UB.top_bind f

@[simp] theorem bot_bind (f : T → Catastrophic U) : bind ⊥ f = ⊥ :=
  Proofs.Semantics.TrackA.Interaction.UB.bot_bind f

theorem bind_eq_top_iff (s : Catastrophic T) (f : T → Catastrophic U) :
    bind s f = ⊤ ↔ s = ⊤ ∨ ∃ t ∈ ordinary s, f t = ⊤ :=
  Proofs.Semantics.TrackA.Interaction.UB.bind_eq_top_iff s f

namespace Arrow

@[simp] theorem id_then (f : Arrow T U) : (Arrow.id T).then f = f := by
  funext t
  exact Subtype.ext (pure_bind t fun a => (f a).val)

@[simp] theorem then_id (f : Arrow T U) : f.then (Arrow.id U) = f := by
  funext t
  exact Subtype.ext (bind_pure (f t).val)

theorem then_assoc {W : Type*} (f : Arrow T U) (g : Arrow U V) (h : Arrow V W) :
    (f.then g).then h = f.then (g.then h) := by
  funext t
  exact Subtype.ext (bind_assoc (f t).val (fun u => (g u).val) (fun v => (h v).val))

theorem then_mono {f f' : Arrow T U} {g g' : Arrow U V} (hf : f ≤ f') (hg : g ≤ g') :
    f.then g ≤ f'.then g' :=
  fun t => bind_mono (hf t) (fun u => hg u)

end Arrow

end Silmaril.Semantics.TrackA.Interaction.UB
