module

public import Silmaril.Compiler.Explorer.Text.Defs

public section

namespace Silmaril.Compiler.Explorer.Proofs

theorem Stage.validated_comp {α β γ : Type} {f : Stage α β} {g : Stage β γ} {R : α → β → Prop}
    {S : β → γ → Prop} (hf : f.validated R) (hg : g.validated S) :
    (f.comp g).validated (fun a c => ∃ b, R a b ∧ S b c) := by
  intro a c h
  simp only [Stage.comp] at h
  cases hb : f.run a with
  | error e => rw [hb] at h; cases h
  | ok b => rw [hb] at h; exact ⟨b, hf a b hb, hg b c h⟩

end Silmaril.Compiler.Explorer.Proofs
