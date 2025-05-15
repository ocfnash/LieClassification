import Mathlib.Algebra.Lie.LieTheorem
import Mathlib.Algebra.Lie.Killing

namespace LieAlgebra

instance {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [FiniteDimensional K L] [HasTrivialRadical K L] :
    IsKilling K L :=
  sorry

end LieAlgebra
