-- FILE: Lean/Lehmer/Data/Pivot/Main.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Data.Pivot.MreqTable : def
- Lehmer.Data.Pivot.Log2Enclosure : def
-/

import Lehmer.Prelude
import Lehmer.Data.Pivot.MreqTable
import Lehmer.Data.Pivot.Log2Enclosure

namespace Lehmer
namespace Data
namespace Pivot

/--
Thin public entry point for raw pivot certificate data.
-/
def pivotDataReady : Bool :=
  true

end Pivot
end Data
end Lehmer