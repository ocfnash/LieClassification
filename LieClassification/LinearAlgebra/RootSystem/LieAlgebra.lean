import Mathlib.Algebra.Lie.CartanExists
import Mathlib.Algebra.Lie.Matrix
import Mathlib.Algebra.Lie.Semisimple.Lemmas
import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Semisimple
import Mathlib.LinearAlgebra.RootSystem.Hom
import LieClassification.Algebra.Lie.Weights.RootSystem
import LieClassification.LinearAlgebra.RootSystem.Base
import LieClassification.LinearAlgebra.RootSystem.CartanMatrix

open LieModule Set

namespace RootPairing

/- In fact `[CommRing R] [IsDomain R]` would suffice for much of the below -/
variable {ι R M N : Type*} [Fintype ι] [DecidableEq ι] [Field R] [CharZero R] [IsAlgClosed R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootSystem ι R M N} [P.IsReduced] [P.IsCrystallographic] [P.IsIrreducible] [P.IsReduced]
  {b : P.Base}

namespace GeckConstruction

instance : (cartanSubalgebra' b).IsCartanSubalgebra := sorry

/-- Equivalent root systems, give equivalent Lie algebras. -/
def lieAlgebraEquiv_of_equiv {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    {P₂ : RootSystem ι₂ R M₂ N₂} [P₂.IsReduced] [P₂.IsCrystallographic] [P₂.IsIrreducible]
    {b₂ : P₂.Base} [Fintype ι₂] [DecidableEq ι₂]
    (e : P.Equiv P₂.toRootPairing) :
    lieAlgebra b ≃ₗ⁅R⁆ lieAlgebra b₂ := by
  -- Need to know Weyl group is transitive on bases but otherwise easy:
  -- construction just uses the values in the pairing.
  sorry

variable (b)

/-- `LieAlgebra.IsKilling.rootSystem` is left inverse to `RootPairing.GeckConstruction.lieAlgebra`.

Lemma 4.6 from [Geck](Geck2017). -/
def rootSystem_cartanSubalgebra_equiv_self :
    (LieAlgebra.IsKilling.rootSystem (cartanSubalgebra' b)).Equiv P.toRootPairing :=
  sorry

open scoped Classical in
/-- `LieAlgebra.IsKilling.rootSystem` is right inverse to `RootPairing.GeckConstruction.lieAlgebra`.
-/
def _root_.LieAlgebra.equiv_rootsystem_lieAlgebra {R L : Type*} [Field R] [CharZero R]
    [LieRing L] [LieAlgebra R L] [FiniteDimensional R L] [LieAlgebra.IsSimple R L]
    (H : LieSubalgebra R L) [H.IsCartanSubalgebra] [IsTriangularizable R H L]
    (b : (LieAlgebra.IsKilling.rootSystem H).Base) :
    L ≃ₗ⁅R⁆ lieAlgebra b :=
  sorry

end GeckConstruction

end RootPairing

namespace LieAlgebra

variable {R L : Type*} [Field R] [CharZero R] [IsAlgClosed R]
  [LieRing L] [LieAlgebra R L] [FiniteDimensional R L] [LieAlgebra.IsSimple R L]

open scoped Classical in
open Module in
/-- Weakest possible form of the classification theorem: over an algebraically closed field, every
finite-dimensional simple Lie algebra arises from a root system. -/
example :
    ∃ (H : LieSubalgebra R L) (_i : H.IsCartanSubalgebra)
      (P : RootSystem H.root R (Dual R H) H) (_ : P.IsCrystallographic)
      (b : P.Base),
      Nonempty (L ≃ₗ⁅R⁆ RootPairing.GeckConstruction.lieAlgebra b) := by
  obtain ⟨x, hx⟩ := exists_isCartanSubalgebra_engel R L
  obtain ⟨b⟩ := (IsKilling.rootSystem (LieSubalgebra.engel R x)).nonempty_base_of_isReduced
  exact ⟨_, hx, _, _, b, ⟨equiv_rootsystem_lieAlgebra (LieSubalgebra.engel R x) b⟩⟩

end LieAlgebra
