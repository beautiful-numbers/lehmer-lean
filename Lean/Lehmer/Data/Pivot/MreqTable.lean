-- FILE: Lean/Lehmer/Data/Pivot/MreqTable.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
-/

import Lehmer.Prelude

namespace Lehmer
namespace Data
namespace Pivot

/--
Metadata wrapper for the external pivot `mreq` table artifact.

Important:
- the currently selected source file is treated here as a raw external artifact;
- this file does not claim to internalize the full table into Lean;
- no theorem in this file claims completeness or exactness of all rows.

This keeps the data layer irreproachable while preserving a stable API hook for
future table ingestion.
-/

def mreqTableSourcePath : String :=
  "data/pivot/mreq_exact_primes_3_to_30000.txt"

def mreqTableSourceSha256 : String :=
  "54ed2c19ca7dd4fe62a9df879beb61eea12408f58189eac030c886a5338e9b3e"

def mreqTableUtf8SourcePath : String :=
  "data/pivot/mreq_exact_primes_3_to_30000.utf8.txt"

def mreqTableUtf8SourceSha256 : String :=
  "d0399d0460d20f6e49d021f5435d9f1372f10c3edadfab07edbba43506075e9c"

def mreqLargeScanSourcePath : String :=
  "data/pivot/mreq_exact_3_to_30000_L50000000.txt"

def mreqLargeScanSourceSha256 : String :=
  "079b159ec339f8f5a4095a9d4593c36dcedc3cf3e43ac35d6d335bed1da76b3d"

/--
A small visible exact prefix, copied from the certificate excerpts already inspected.

This is intentionally only a prefix sample. It is not advertised as the complete
table for all primes `< 30000`.
-/
def mreqPrimeTablePrefix : List (ℕ × ℕ) :=
  [ (3, 3),
    (5, 7),
    (7, 15),
    (11, 27),
    (13, 41),
    (17, 62),
    (19, 85),
    (23, 115),
    (29, 150),
    (31, 186),
    (37, 229),
    (41, 274),
    (43, 323),
    (47, 380),
    (53, 443),
    (59, 509),
    (61, 577),
    (67, 653),
    (71, 733),
    (73, 818),
    (79, 912),
    (83, 1010),
    (89, 1114),
    (97, 1222),
    (101, 1331),
    (103, 1448),
    (107, 1572),
    (109, 1704),
    (113, 1845),
    (127, 1994),
    (131, 2138),
    (137, 2289),
    (139, 2445),
    (149, 2609),
    (151, 2774),
    (157, 2948),
    (163, 3127),
    (167, 3311),
    (173, 3502),
    (179, 3699),
    (181, 3900),
    (191, 4112),
    (193, 4324),
    (197, 4546),
    (199, 4775) ]

def mreqPrimeTablePrefixLookup (y : ℕ) : Option ℕ :=
  (mreqPrimeTablePrefix.find? (fun p => p.1 = y)).map Prod.snd

/--
The selected canonical artifact is not yet represented in Lean as a complete
internal table. This boolean is a data-layer flag, not a theorem.
-/
def mreqPrimeTableInternalizedCompletely : Bool := false

end Pivot
end Data
end Lehmer