-- FILE: Lean/Lehmer/Data/Pivot/Log2Enclosure.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
-/

import Lehmer.Prelude

namespace Lehmer
namespace Data
namespace Pivot

/--
Raw endpoint certificate data for the Appendix A large-range pivot check at `Y0 = 30000`.

This file deliberately stores certificate values as data only.
Decimal quantities are kept as strings to avoid introducing parsing or arithmetic
machinery at the data layer.
-/

def pivotAProofSourcePath : String :=
  "data/pivot/pivotA_proof_Y0=30000.txt"

def pivotAProofSourceSha256 : String :=
  "10e522653f533488d6676d19c0c570501c2907eb81a3038542c3071e5365e3f4"

def pivotA_C1_num : ℕ := 1
def pivotA_C1_den : ℕ := 1000

def pivotA_Y0 : ℕ := 30000
def pivotA_y : ℕ := 30000
def pivotA_endpoint_m : ℕ := 87302
def pivotA_endpoint_n : ℕ := 117301

def pivotA_mertens_ref : String :=
  "Axler/Rosser–Schoenfeld style: |sum_{p<=x} 1/p - (log log x + B1)| <= c/log x"

def pivotA_mertens_x0 : ℕ := 55
def pivotA_mertens_B1 : String := "0.2614972128"
def pivotA_mertens_c : String := "1.0"

def pivotA_nthPrime_ref : String :=
  "Dusart (2010): p_n <= n(log n + log log n) for n>=6"

def pivotA_nthPrime_n0 : ℕ := 6

def pivotA_decimal_prec : ℕ := 120
def pivotA_ln2_terms : ℕ := 40

def pivotA_ln2_lb : String :=
  "0.693147180559945309417232121458176568075437678466266780328030014916188517807030021382184919630689846819390140241431223410"

def pivotA_ln2_ub : String :=
  "0.693147180559945309417232121458176568075500321944981459741608847965060096618377022173883765799635332776706407141448778870"

def pivotA_x_upper : String :=
  "1657431.93781419732352402860786309430288438431142506019266048384514050488159573557265111697126294662423425309952345021787"

def pivotA_loglog_x_upper : String :=
  "2.66171162492644986225646812085809355503974029807441558156852267049801967311842447481646069078719892614617734731919337208"

def pivotA_loglog_y : String :=
  "2.33301270806221545927777535546117865288409393352371641948750485210665170959404036482488389728496064386885835821284500130"

def pivotA_c_over_log_x_upper : String :=
  "0.0698285990285721654576804798530007302216812661515191676399153819186734269363664845266067789639876918223900722123675567301"

def pivotA_c_over_log_y : String :=
  "0.0970030645128116884856547668401384818435829175353931748775299373615004310094144806127874827996892782483848531854940270217"

def pivotA_inv_y_minus_one : String :=
  "0.0000333344444814827160905363512117070569018967298909963665455515183839461315377179239307976932564418813960465348844961498717"

def pivotA_rhs_upper : String :=
  "0.495563914850099739638118548441265821277812444967502500965008689189925767601702793054901852959171694229489961039094450682"

def pivotA_nthPrimeBoundUsed : Bool := true
def pivotA_mertensUsableAtEndpoint : Bool := true
def pivotA_endpoint_ok : Bool := true

end Pivot
end Data
end Lehmer