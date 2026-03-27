import Mathlib.Algebra.Lie.CartanExists
import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Basis
import LieClassification.Algebra.Lie.CartanCriterion
import LieClassification.LinearAlgebra.RootSystem.CartanMatrix

open LieModule Module

namespace RootPairing.GeckConstruction

variable {ι R M N : Type*} [Fintype ι] [DecidableEq ι] [Field R] [CharZero R] [IsAlgClosed R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic] [P.IsIrreducible]
  (b : P.Base)

open scoped Classical in
/-- `LieAlgebra.IsKilling.rootSystem` is right inverse to `RootPairing.GeckConstruction.lieAlgebra`.
-/
def _root_.LieAlgebra.equiv_rootsystem_lieAlgebra {R L : Type*} [Field R] [CharZero R]
    [LieRing L] [LieAlgebra R L] [FiniteDimensional R L] [LieAlgebra.IsSimple R L]
    (H : LieSubalgebra R L) [H.IsCartanSubalgebra] [IsTriangularizable R H L]
    (b : (LieAlgebra.IsKilling.rootSystem H).Base) :
    L ≃ₗ⁅R⁆ lieAlgebra b :=
  sorry

end RootPairing.GeckConstruction

open LieAlgebra

variable {R L : Type*} [Field R] [CharZero R] [IsAlgClosed R]
  [LieRing L] [LieAlgebra R L] [FiniteDimensional R L] [LieAlgebra.IsSimple R L]

open scoped Classical in
/-- Weakest possible form of the classification theorem: over an algebraically closed field, every
finite-dimensional simple Lie algebra arises from a root system. -/
example :
    ∃ (H : LieSubalgebra R L) (_i : H.IsCartanSubalgebra)
      (P : RootPairing H.root R (Dual R H) H) (_ : P.IsCrystallographic) (b : P.Base),
      Nonempty (L ≃ₗ⁅R⁆ RootPairing.GeckConstruction.lieAlgebra b) := by
  obtain ⟨x, hx⟩ := exists_isCartanSubalgebra_engel R L
  obtain ⟨b⟩ := (IsKilling.rootSystem (LieSubalgebra.engel R x)).nonempty_base
  exact ⟨_, hx, _, _, b, ⟨equiv_rootsystem_lieAlgebra (LieSubalgebra.engel R x) b⟩⟩
