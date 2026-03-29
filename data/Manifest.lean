-- FILE: Lean/Lehmer/Data/Manifest.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
-/

import Lehmer.Prelude

namespace Lehmer
namespace Data

/--
Repository-level manifest entries for proof-relevant external data artifacts.

These constants mirror the raw files stored under `data/`.
They are informational only: no proof in this file depends on recomputing hashes.
-/

def manifestPath : String := "data/manifests/manifest.sha256"

namespace Pivot

def pivotOnlyY3_200_path : String :=
  "data/pivot/pivot_only_y3_200.txt"

def pivotAProofY0_30000_path : String :=
  "data/pivot/pivotA_proof_Y0=30000.txt"

def mreqExactPrimes_3_to_30000_path : String :=
  "data/pivot/mreq_exact_primes_3_to_30000.txt"

def mreqExactPrimes_3_to_30000_utf8_path : String :=
  "data/pivot/mreq_exact_primes_3_to_30000.utf8.txt"

def mreqExact_3_to_30000_L50000000_path : String :=
  "data/pivot/mreq_exact_3_to_30000_L50000000.txt"

/-
Hashes copied from the repository manifest shown by the user.
-/

def pivotOnlyY3_200_sha256 : String :=
  "bfd5b9d2c85c901f2e3839863a00062e9af404006568d62b517b910e0a470905"

def pivotAProofY0_30000_sha256 : String :=
  "10e522653f533488d6676d19c0c570501c2907eb81a3038542c3071e5365e3f4"

def mreqExactPrimes_3_to_30000_sha256 : String :=
  "54ed2c19ca7dd4fe62a9df879beb61eea12408f58189eac030c886a5338e9b3e"

def mreqExactPrimes_3_to_30000_utf8_sha256 : String :=
  "d0399d0460d20f6e49d021f5435d9f1372f10c3edadfab07edbba43506075e9c"

def mreqExact_3_to_30000_L50000000_sha256 : String :=
  "079b159ec339f8f5a4095a9d4593c36dcedc3cf3e43ac35d6d335bed1da76b3d"

end Pivot
end Data
end Lehmer