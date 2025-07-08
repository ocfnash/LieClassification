import Mathlib.Algebra.Lie.CartanExists
import Mathlib.Algebra.Lie.Matrix
import Mathlib.Algebra.Lie.Semisimple.Lemmas
import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Basic
import Mathlib.LinearAlgebra.RootSystem.Hom
import LieClassification.Algebra.Lie.Weights.RootSystem
import LieClassification.LinearAlgebra.RootSystem.Base
import LieClassification.LinearAlgebra.RootSystem.CartanMatrix
import LieClassification.LinearAlgebra.RootSystem.Chain

open LieModule Set

namespace RootPairing

/- In fact `[CommRing R] [IsDomain R]` would suffice for much of the below -/
variable {ι R M N : Type*} [Finite ι] [Field R] [CharZero R] [IsAlgClosed R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootSystem ι R M N} [P.IsReduced] [P.IsCrystallographic] [P.IsIrreducible]
  {b : P.Base}

namespace GeckConstruction

-- Easy using `RootPairing.Base.cartanMatrix_nondegenerate`
lemma linearIndependent_h :
    LinearIndependent (ι := b.support) R h := by
  sorry

variable [P.IsReduced] [Fintype ι] [DecidableEq ι]

/-- RootSystemLemma 4.2 from [Geck](Geck2017).

Will need `RootPairing.Base.cartanMatrix_sub_four_det_ne_zero`. -/
instance : LieModule.IsIrreducible R (lieAlgebra b) (b.support ⊕ ι → R) := sorry

variable (b) in
abbrev cartanSubalgebra' := (cartanSubalgebra b).comap (lieAlgebra b).incl

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

lemma trace_toEnd_eq_zero (x : lieAlgebra b) :
    LinearMap.trace R _ (toEnd R _ (b.support ⊕ ι → R) x) = 0 :=
  sorry

/-- Lemma 4.3 from [Geck](Geck2017). -/
instance : LieAlgebra.HasTrivialRadical R (lieAlgebra b) :=
  LieAlgebra.hasTrivialRadical_of_isIrreducible_of_isFaithful R _ _ (trace_toEnd_eq_zero b)

/-- `LieAlgebra.IsKilling.rootSystem` is left inverse to `RootSystem.lieAlgebra`.

Lemma 4.6 from [Geck](Geck2017). -/
def rootSystem_cartanSubalgebra_equiv_self :
    (LieAlgebra.IsKilling.rootSystem (cartanSubalgebra' b)).Equiv P.toRootPairing :=
  sorry

open scoped Classical in
/-- `LieAlgebra.IsKilling.rootSystem` is right inverse to `RootSystem.lieAlgebra`. -/
def _root_.LieAlgebra.equiv_rootsystem_lieAlgebra {R L : Type*} [Field R] [CharZero R]
    [LieRing L] [LieAlgebra R L] [FiniteDimensional R L] [LieAlgebra.IsSimple R L]
    (H : LieSubalgebra R L) [H.IsCartanSubalgebra] [IsTriangularizable R H L]
    (b : (LieAlgebra.IsKilling.rootSystem H).Base) [Fintype b.support] :
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
