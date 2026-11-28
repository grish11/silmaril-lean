module

public import Silmaril.Machine.SQLite.Pager.Defs
public import Silmaril.Machine.SQLite.TrackB.Read.Defs
public import Silmaril.Machine.SQLite.Relational.Bridge.Defs

/-!
The file image can contain several trees and other page kinds. A B-tree
position selects a page within a tree layout, while a VFS path selects an
entire byte backing. The numbered-page representation and the ordered map
observe different aspects of a B-tree. The SQLite decoder bridge admits
only a caller-designated 512-byte packed rowid leaf.
-/
