import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Lemmas

namespace RootPairing

open Set

variable {ι R M N : Type*} [Finite ι] [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic]
  {b : P.Base} {i j k l m : ι}
  (hi : i ∈ b.support) (hj : j ∈ b.support) (hij : i ≠ j)
  (h₁ : P.root k + P.root i = P.root l)
  (h₂ : P.root k - P.root j = P.root m)
  (h₃ : P.root k + P.root i - P.root j ∈ range P.root)

include hi hj hij h₁ h₂ h₃

private lemma chainBotCoeff_mul_chainTopCoeff.aux_3 :
    P.IsNotG2 :=
  sorry

/-- This is `RootPairing.chainBotCoeff_mul_chainTopCoeff` except without the redundant
assumption `[P.IsNotG2]`.

Once this has been proved, we can drop `[P.IsNotG2]` from the downstream lemma
`RootPairing.GeckConstruction.lie_e_f_ne`. -/
lemma chainBotCoeff_mul_chainTopCoeff' :
    (P.chainBotCoeff i m + 1) * (P.chainTopCoeff j k + 1) =
      (P.chainTopCoeff j l + 1) * (P.chainBotCoeff i k + 1) :=
  have : P.IsNotG2 := chainBotCoeff_mul_chainTopCoeff.aux_3 hi hj hij h₁ h₂ h₃
  chainBotCoeff_mul_chainTopCoeff hi hj hij h₁ h₂ h₃

end RootPairing
