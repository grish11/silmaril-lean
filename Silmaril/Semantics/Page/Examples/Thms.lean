module

public import Silmaril.Semantics.Page.Examples.Defs
public import Silmaril.Semantics.Page.Thms
import Silmaril.Proofs.Semantics.Page.Examples

public section
namespace Silmaril.Semantics.Page.Examples

theorem initializeThenRead_correct :
    ForallCorrect (singlePage Bool) initializeThenRead (uninitialized Bool)
      (fun value final image => value = true ∧ final 0 = .defined true ∧ image 0 = some true) :=
  Proofs.initializeThenRead_correct

theorem forbidden_read :
    Run (singlePage Bool) (Program.read 0) (uninitialized Bool) [] (.stopped (.ub (.readUndef 0))) :=
  Proofs.forbidden_read

theorem forbidden_read_not_correct :
    ¬ ExistsCorrect (singlePage Bool) (Program.read 0) (uninitialized Bool) (fun _ _ _ => True) :=
  Proofs.forbidden_read_not_correct

theorem allocation_exhausted :
    Run (singlePage Bool) Program.allocate (uninitialized Bool) [] (.returned none (uninitialized Bool)) :=
  Proofs.allocation_exhausted

theorem deallocate_then_allocate :
    Run (singlePage Bool) ((Program.deallocate 0).bind fun _ => Program.allocate) (uninitialized Bool)
      [.deallocate 0, .allocate 0] (.returned (some 0) (uninitialized Bool)) :=
  Proofs.deallocate_then_allocate

theorem existential_bind_counterexample :
    ExistsCorrect (singlePage Bool) chooseBit (uninitialized Bool) (fun _ m _ => m = uninitialized Bool) ∧
    (∀ bit m, m = uninitialized Bool → ExistsCorrect (singlePage Bool) (.pure bit) m bitPost) ∧
    ¬ ExistsCorrect (singlePage Bool) (chooseBit.bind Program.pure) (uninitialized Bool) bitPost :=
  Proofs.existential_bind_counterexample

theorem final_image_distinctions :
    ExistsCorrect (singlePage Bool) (.pure true) (uninitialized Bool) bitPost ∧
    ¬ ForallCorrect (singlePage Bool) (.pure true) (uninitialized Bool) bitPost ∧
    ForallCorrect (singlePage Bool) (.pure ()) (uninitialized Bool) (fun _ _ image => image 0 ≠ none) ∧
    ¬ Correct (singlePage Bool) (.pure ()) (uninitialized Bool)
      (fun _ m => definedImage (singlePage Bool) m 0 ≠ none) :=
  Proofs.final_image_distinctions

theorem empty_contents :
    ForallCorrect (singlePage PEmpty) (.pure ()) (empty PEmpty) (fun _ _ _ => True) ∧
    ¬ ForallCorrect (singlePage PEmpty) (.pure ()) (uninitialized PEmpty) (fun _ _ _ => True) ∧
    ¬ ForallCorrect (singlePage PEmpty) Program.allocate (empty PEmpty) (fun _ _ _ => True) :=
  Proofs.empty_contents

end Silmaril.Semantics.Page.Examples
