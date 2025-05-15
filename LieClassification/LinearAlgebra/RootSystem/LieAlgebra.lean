import Mathlib.Algebra.Lie.CartanExists
import Mathlib.Algebra.Lie.Semisimple.Lemmas
import Mathlib.LinearAlgebra.RootSystem.Hom
import LieClassification.Algebra.Lie.Weights.RootSystem
import LieClassification.LinearAlgebra.RootSystem.Base
import LieClassification.LinearAlgebra.RootSystem.CartanMatrix
import LieClassification.LinearAlgebra.RootSystem.Chain

open LieModule Set

namespace RootPairing

/- In fact `[CommRing R] [IsDomain R]` would suffice for much of the below -/
variable {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootSystem ι R M N} [P.IsReduced] [P.IsCrystallographic] [P.IsIrreducible]
  {b : P.Base}

namespace LieAlgebra

/-- NB: We could also define these to have type `Module.End R (M × (ι → R))` but it would require
invoking `b.toWeightBasis.equivFun` in their definitions so this is probably simplest.

Note that we could also define these as having type `Module.End ℕ ((b.support → R) × (ι → R))` but
I think not worth the trouble (at least for now). -/
def e (i : b.support) : Module.End R ((b.support → R) × (ι → R)) := sorry

def f (i : b.support) : Module.End R ((b.support → R) × (ι → R)) := sorry

def h (i : b.support) : Module.End R ((b.support → R) × (ι → R)) := sorry

/-- Lemma 3.3 (a) from [Geck](Geck2017).

TODO Add part (b) as well as Lemmas 3.4, 3.5. -/
lemma lie_h_e (i j : b.support) :
    ⁅h j, e i⁆ = P.pairingIn ℤ i j • e i :=
  sorry

end LieAlgebra

namespace Base

variable (b)

/-- The Lie algebra associated to a root system with distinguished base. -/
def lieAlgebra :
    LieSubalgebra R (Module.End R ((b.support → R) × (ι → R))) :=
  LieSubalgebra.lieSpan R _ (range LieAlgebra.e ∪ range LieAlgebra.f)

/-- The Cartan subalgebra of the Lie algebra associated to a root system with distinguished base. -/
def cartanSubalgebra :
    LieSubalgebra R (lieAlgebra b) :=
  (LieSubalgebra.lieSpan R _ (range LieAlgebra.h)).comap (lieAlgebra b).incl

/-- Equivalent root systems, give equivalent Lie algebras. -/
def lieAlgebraEquiv_of_equiv {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    {P₂ : RootSystem ι₂ R M₂ N₂} [P₂.IsReduced] [P₂.IsCrystallographic] [P₂.IsIrreducible]
    {b₂ : P₂.Base}
    (e : P.Equiv P₂.toRootPairing) :
    b.lieAlgebra ≃ₗ⁅R⁆ b₂.lieAlgebra := by
  -- Need to know Weyl group is transitive on bases but otherwise easy:
  -- construction just uses the values in the pairing.
  sorry

-- Trivial
instance : FiniteDimensional R (lieAlgebra b) := sorry

instance : (cartanSubalgebra b).IsCartanSubalgebra where
  nilpotent := sorry -- Easy (because Abelian)
  self_normalizing := sorry -- Lemma 4.5 from [Geck](Geck2017)

/-- We can make this trivial by just assuming algebraically closed. -/
instance : IsTriangularizable R (cartanSubalgebra b) (lieAlgebra b) := sorry

/-- We can make this trivial by just assuming algebraically closed. -/
instance : IsTriangularizable R (lieAlgebra b) ((b.support → R) × (ι → R)) := sorry

/-- RootSystemLemma 4.2 from [Geck](Geck2017).

Will need `RootPairing.Base.cartanMatrix_sub_four_det_ne_zero`. Will also need some more API
for root system bases. -/
instance : LieModule.IsIrreducible R (lieAlgebra b) ((b.support → R) × (ι → R)) := sorry

-- Trivial (it's a subalgebra)
instance : IsFaithful R (lieAlgebra b) ((b.support → R) × (ι → R)) := sorry

-- Easy
lemma trace_toEnd_eq_zero (x : lieAlgebra b) :
    LinearMap.trace R _ (toEnd R _ ((b.support → R) × (ι → R)) x) = 0 :=
  sorry

/-- Lemma 4.3 from [Geck](Geck2017). -/
instance : LieAlgebra.HasTrivialRadical R (lieAlgebra b) :=
  LieAlgebra.hasTrivialRadical_and_of_isIrreducible_of_isFaithful R _ _ (trace_toEnd_eq_zero b)

/-- `LieAlgebra.IsKilling.rootSystem` is left inverse to `RootSystem.lieAlgebra`.

Lemma 4.6 from [Geck](Geck2017). -/
def rootSystem_cartanSubalgebra_equiv_self :
    (LieAlgebra.IsKilling.rootSystem (cartanSubalgebra b)).Equiv P.toRootPairing :=
  sorry

/-- `LieAlgebra.IsKilling.rootSystem` is right inverse to `RootSystem.lieAlgebra`. -/
def _root_.LieAlgebra.equiv_rootsystem_lieAlgebra {R L : Type*} [Field R] [CharZero R]
    [LieRing L] [LieAlgebra R L] [FiniteDimensional R L] [LieAlgebra.IsSimple R L]
    (H : LieSubalgebra R L) [H.IsCartanSubalgebra] [IsTriangularizable R H L]
    (b : (LieAlgebra.IsKilling.rootSystem H).Base) :
    L ≃ₗ⁅R⁆ lieAlgebra b :=
  sorry

end Base

end RootPairing

namespace LieAlgebra

variable {R L : Type*} [Field R] [CharZero R] [IsAlgClosed R]
  [LieRing L] [LieAlgebra R L] [FiniteDimensional R L] [LieAlgebra.IsSimple R L]

open Module in
/-- Weakest possible form of the classification theorem: over an algebraically closed field, every
finite-dimensional simple Lie algebra arises from a root system. -/
example :
    ∃ (H : LieSubalgebra R L) (_i : H.IsCartanSubalgebra)
      (P : RootSystem H.root R (Dual R H) H) (b : P.Base),
      Nonempty (L ≃ₗ⁅R⁆ b.lieAlgebra) := by
  obtain ⟨x, hx⟩ := exists_isCartanSubalgebra_engel R L
  obtain ⟨b⟩ := (IsKilling.rootSystem (LieSubalgebra.engel R x)).nonempty_base_of_isReduced
  exact ⟨_, hx, _, b, ⟨equiv_rootsystem_lieAlgebra (LieSubalgebra.engel R x) b⟩⟩

end LieAlgebra
