import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

namespace RootPairing.Base

variable {ι R M N : Type*} [Finite ι] [DecidableEq ι] [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} (b : P.Base)
  [P.IsCrystallographic]

/-- A (finite-type) Cartan matrix cannot have eigenvalue `4`. -/
lemma cartanMatrix_sub_four_det_ne_zero :
    (4 - b.cartanMatrix).det ≠ 0 :=
  -- Should be able to prove this via Perron-Frobenius as outlined here:
  -- https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/Eigenvalues.20of.20Cartan.20matrices/near/516844801
  sorry

-- Once `RootPairing.Base.cartanMatrix_sub_four_det_ne_zero` is proved we can drop this `Fact`
-- entirely by just using `RootPairing.Base.cartanMatrix_sub_four_det_ne_zero` in the proof of
-- `RootPairing.GeckConstruction.instIsIrreducible` instead.
instance : Fact ((4 - b.cartanMatrix).det ≠ 0) := ⟨b.cartanMatrix_sub_four_det_ne_zero⟩

end RootPairing.Base
