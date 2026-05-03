-- FILE: Lean/Lehmer/Verify.lean

import Lehmer.Final.MainTheorem
import Lehmer.Final.NoCompositeLehmer
import Lehmer.Audit.PierreDeFermat

/- Main / final pipeline endpoints -/

#check Lehmer.Final.main_theorem_of_pipeline_closure
#print axioms Lehmer.Final.main_theorem_of_pipeline_closure

#check Lehmer.Final.no_LehmerComposite_of_pipeline_closure
#print axioms Lehmer.Final.no_LehmerComposite_of_pipeline_closure

#check Lehmer.Final.no_composite_Lehmer_of_pipeline_closure
#print axioms Lehmer.Final.no_composite_Lehmer_of_pipeline_closure

#check Lehmer.Final.LehmerComposite_implies_false_of_pipeline_closure
#print axioms Lehmer.Final.LehmerComposite_implies_false_of_pipeline_closure

/- Audit / referee endpoints -/

#check Lehmer.Audit.pierreDeFermat_of_range_closures
#print axioms Lehmer.Audit.pierreDeFermat_of_range_closures

#check Lehmer.Audit.no_LehmerComposite_of_range_closures
#print axioms Lehmer.Audit.no_LehmerComposite_of_range_closures

#check Lehmer.Audit.no_counterexample_of_range_closures
#print axioms Lehmer.Audit.no_counterexample_of_range_closures