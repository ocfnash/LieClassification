import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.LinearAlgebra.RootSystem.Irreducible
import LieClassification.Algebra.Lie.CartanCriterion

namespace LieAlgebra.IsKilling

open LieModule

variable {K L : Type*}
  [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]

lemma isSimple_of_isIrreducible_rootSystem [IsSemisimple K L] (h : (rootSystem H).IsIrreducible) :
    IsSimple K L :=
  sorry

end LieAlgebra.IsKilling
