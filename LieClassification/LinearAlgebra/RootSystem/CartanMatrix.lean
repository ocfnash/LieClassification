import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

namespace RootPairing.Base

variable {ι R M N : Type*} [Finite ι] [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} (b : P.Base)
  [P.IsCrystallographic]

/-- A (finite-type) Cartan matrix cannot have eigenvalue `4`. -/
lemma cartanMatrix_sub_four_det_ne_zero [Fintype b.support] [DecidableEq b.support] :
    (b.cartanMatrix - 4 • 1).det ≠ 0 :=
  -- Should be able to prove this via Perron-Frobenius as outlined here:
  -- https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/Eigenvalues.20of.20Cartan.20matrices/near/516844801
  sorry

end RootPairing.Base
