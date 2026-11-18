module
public import Silmaril.Elf.Corpus.SqliteBuildQueries.Source.Projection.Defs
@[expose] public section
set_option cbv.maxSteps 4000000
namespace Silmaril.Elf.Corpus.SqliteBuildQueries.Source.Projection
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem byte_projection : exact := by
  unfold exact
  decide +kernel
end Silmaril.Elf.Corpus.SqliteBuildQueries.Source.Projection
