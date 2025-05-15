import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.RootSystem.Reduced

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [P.IsReduced] [P.IsCrystallographic]

lemma nonempty_base_of_isReduced :
    Nonempty P.Base :=
  sorry

end RootPairing
