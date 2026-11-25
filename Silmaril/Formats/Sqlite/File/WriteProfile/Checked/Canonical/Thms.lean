module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Checked.Defs
import Silmaril.Proofs.Formats.Sqlite.File.WriteProfile.Checked.Canonical.Read

public section
namespace Silmaril.Formats.Sqlite.WriteProfile.Image.Checked

/-- A permutation of unique typed rows preserves the exact checked writer
outcome, including the emitted bytes and typed errors. -/
theorem encode_perm {left right : Snapshot} (rows : left.rows.Perm right.rows) :
    encode left = encode right :=
  Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.Checked.Canonical.encode_perm rows

end Silmaril.Formats.Sqlite.WriteProfile.Image.Checked
