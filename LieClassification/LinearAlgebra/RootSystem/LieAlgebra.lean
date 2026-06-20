import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Basis
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.CartanExists
import Mathlib.Algebra.Lie.Weights.IsSimple

noncomputable section

namespace LieAlgebra

open IsKilling

variable
  {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
  {L : Type*} [LieRing L] [LieAlgebra K L] [FiniteDimensional K L] [IsSimple K L]

/-- Given two Lie algebras with distinguished Cartan subalgebras, an equivalence of the associated
root systems determines an equivalence of the Lie algebras. -/
def equivOfRootSystemEquiv
    {L' : Type*} [LieRing L'] [LieAlgebra K L'] [FiniteDimensional K L'] [IsSimple K L']
    {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
    {H' : LieSubalgebra K L'} [H'.IsCartanSubalgebra]
    (e : (rootSystem H).Equiv (rootSystem H')) :
    L ≃ₗ⁅K⁆ L' :=
  sorry

instance (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [DecidableEq H.root]
    (b : (rootSystem H).Base) :
    IsSimple K (RootPairing.GeckConstruction.lieAlgebra b) := by
  -- Trivial via `LieAlgebra.IsKilling.isSimple_iff_isIrreducible`
  sorry

open scoped Classical in
/-- `LieAlgebra.IsKilling.rootSystem` is right inverse to `RootPairing.GeckConstruction.lieAlgebra`.
-/
def equivGeckConstruction (H : LieSubalgebra K L) [H.IsCartanSubalgebra]
    (b : (rootSystem H).Base) :
    L ≃ₗ⁅K⁆ RootPairing.GeckConstruction.lieAlgebra b :=
  equivOfRootSystemEquiv <| RootPairing.GeckConstruction.equivRootSystem b

open scoped Classical in
/-- Weakest possible form of the classification theorem: over an algebraically closed field, every
finite-dimensional simple Lie algebra arises from a root system. -/
example :
    ∃ (H : LieSubalgebra K L) (_ : H.IsCartanSubalgebra) (b : (rootSystem H).Base),
      Nonempty (L ≃ₗ⁅K⁆ RootPairing.GeckConstruction.lieAlgebra b) := by
  obtain ⟨x, hx⟩ := exists_isCartanSubalgebra_engel K L
  obtain ⟨b⟩ := (rootSystem (LieSubalgebra.engel K x)).nonempty_base
  exact ⟨_, hx, b, ⟨equivGeckConstruction (LieSubalgebra.engel K x) b⟩⟩

end LieAlgebra
