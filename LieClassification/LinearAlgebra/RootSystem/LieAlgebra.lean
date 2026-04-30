import Mathlib.Algebra.Lie.CartanExists
import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Basis
import Mathlib.Algebra.Lie.CartanCriterion
import LieClassification.LinearAlgebra.RootSystem.CartanMatrix

open LieModule LieAlgebra LieAlgebra.IsKilling

variable
  {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
  {L : Type*} [LieRing L] [LieAlgebra K L] [FiniteDimensional K L] [IsSimple K L]

open scoped Classical in
/-- `LieAlgebra.IsKilling.rootSystem` is right inverse to `RootPairing.GeckConstruction.lieAlgebra`.
-/
def _root_.LieAlgebra.equiv_rootsystem_lieAlgebra (H : LieSubalgebra K L) [H.IsCartanSubalgebra]
    (b : (LieAlgebra.IsKilling.rootSystem H).Base) :
    L ≃ₗ⁅K⁆ RootPairing.GeckConstruction.lieAlgebra b :=
  sorry

open scoped Classical in
/-- Weakest possible form of the classification theorem: over an algebraically closed field, every
finite-dimensional simple Lie algebra arises from a root system. -/
example :
    ∃ (H : LieSubalgebra K L) (_ : H.IsCartanSubalgebra) (b : (rootSystem H).Base),
      Nonempty (L ≃ₗ⁅K⁆ RootPairing.GeckConstruction.lieAlgebra b) := by
  obtain ⟨x, hx⟩ := exists_isCartanSubalgebra_engel K L
  obtain ⟨b⟩ := (IsKilling.rootSystem (LieSubalgebra.engel K x)).nonempty_base
  exact ⟨_, hx, b, ⟨equiv_rootsystem_lieAlgebra (LieSubalgebra.engel K x) b⟩⟩
