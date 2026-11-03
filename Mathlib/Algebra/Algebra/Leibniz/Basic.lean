/-
Copyright (c) 2026 Viviana del Barco, Gustavo Infanti, Exequiel Rivas and Paul Schwahn.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Viviana del Barco, Gustavo Infanti, Exequiel Rivas, Paul Schwahn
-/
module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Algebra.Algebra.NonUnitalIdeal

import Aesop.BuiltinRules
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Module
import Mathlib.Tactic.TypeStar
/-!
# Leibniz rings and algebras

A **right Leibniz ring** is a non-unital, non-associative ring satisfying
`(x * y) * z = (x * z) * y + x * (y * z)` for all `x`, `y`, and `z`.

We study Leibniz algebras by additionally assuming a module structure
with bilinear multiplication.

## Main definitions

* `IsLeibniz`: the right Leibniz identity.
* `Submodule.spanOfSquares`: the linear span of the squares `x * x`.
* `Submodule.spanOfMulSubmodules`: the linear span of products between two submodules
  in both orders.
* `NonUnitalNonAssocSemiring.IsSkew`: the condition that every element squares to zero.

## Main results

* `Leibniz.mul_left_mul_self`: multiplying a square on the left by any element gives zero.
* `Leibniz.squareSpan_left_mul_mem` and `Leibniz.squareSpan_right_mul_mem`: the span of
  squares is stable under left and right multiplication, assuming the corresponding
  compatibility with scalar multiplication.
* `Leibniz.instLieRing` and `Leibniz.instLieAlgebra`: a Leibniz ring or algebra in which
  every element squares to zero carries a Lie structure with bracket given by multiplication.
* `Leibniz.ofLieRing`: every Lie ring satisfies the right Leibniz identity when its bracket
  is used as multiplication.

## Implementation notes

`Leibniz.ofLieRing` uses the ring structure `LieRing.toNonUnitalNonAssocRing` explicitly;
it does not install a global multiplication on Lie rings.

## References

* https://en.wikipedia.org/wiki/Leibniz_algebra
-/

public section

/-- The right Leibniz identity for a non-unital, non-associative ring. -/
@[mk_iff isLeibniz_iff]
class IsLeibniz (A : Type*) [NonUnitalNonAssocRing A] : Prop where
  leibniz' (x y z : A) : (x * y) * z = (x * z) * y + x * (y * z)

namespace Leibniz

variable {A : Type*} [NonUnitalNonAssocRing A] [IsLeibniz A]

/-- The right Leibniz identity. -/
theorem leibniz (x y z : A) : (x * y) * z = (x * z) * y + x * (y * z) :=
  IsLeibniz.leibniz' x y z

/-- The right Leibniz identity expressed as a formula for `x * (y * z)`. -/
theorem mul_left_mul (x y z : A) : x * (y * z) = (x * y) * z - (x * z) * y := by
  rw [leibniz]
  simp only [add_sub_cancel_left]

/-- Multiplying a square on the left by any element gives zero. -/
theorem mul_left_mul_self (x z : A) : z * (x * x) = 0 := by
  rw [mul_left_mul]
  simp only [sub_self]

/-- Swapping the factors of the inner product negates `x * (y * z)`. -/
theorem mul_left_mul_anticomm (x y z : A) : x * (y * z) = - (x * (z * y)) := by
  rw [mul_left_mul, mul_left_mul]
  simp only [neg_sub]

end Leibniz

namespace Submodule

/-- The `R`-linear span of the squares `x * x` in `A`. -/
def spanOfSquares (R A : Type*) [Semiring R] [NonUnitalNonAssocRing A] [Module R A]
    : Submodule R A :=
  Submodule.span R (Set.range fun x : A => x * x)

/-- Every symmetrized product belongs to the span of squares. -/
theorem symm_SpanOfSquares_mem {R A : Type*} [Ring R] [NonUnitalNonAssocRing A] [Module R A]
    (x y : A) : x * y + y * x ∈ spanOfSquares R A:= by
  have : x * y + y * x = (x + y) * (x + y) - x * x - y * y := by
    rw [add_mul, mul_add,mul_add]
    abel
  rw [this]
  refine sub_mem (sub_mem ?_ ?_) ?_ <;> exact Submodule.subset_span ⟨_, rfl⟩

/-- The `R`-linear span of all products `u * v` and `v * u` with `u ∈ U` and `v ∈ V`. -/
def spanOfMulSubmodules {R A : Type*} [Semiring R] [NonUnitalNonAssocRing A] [Module R A]
    (U V : Submodule R A) : Submodule R A := Submodule.span R
    (Set.range (fun p : U × V => (p.1 : A) * (p.2 : A)) ∪
      Set.range (fun p : V × U => (p.1 : A) * (p.2 : A)))

/-- A product of elements of `U` and `V` belongs to their product span. -/
@[simp]
theorem mem_bracketSpan_of_mem {R A : Type*} [Semiring R] [NonUnitalNonAssocRing A] [Module R A]
    {U V : Submodule R A} {x y : A} (hx : x ∈ U) (hy : y ∈ V) :
    x * y ∈ spanOfMulSubmodules (R := R) (A := A) U V :=
  Submodule.subset_span (Or.inl ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩)

/-- A product in the reverse order also belongs to the product span of `U` and `V`. -/
@[simp]
theorem mem_bracketSpan_of_mem_swap {R A : Type*} [Semiring R] [NonUnitalNonAssocRing A]
    [Module R A] {U V : Submodule R A} {x y : A} (hx : x ∈ U) (hy : y ∈ V) :
    y * x ∈ spanOfMulSubmodules (R := R) (A := A) U V :=
  Submodule.subset_span (Or.inr ⟨(⟨y, hy⟩, ⟨x, hx⟩), rfl⟩)

end Submodule

namespace Leibniz

open Submodule

/-- The span of squares is stable under left multiplication in a right Leibniz ring. -/
lemma squareSpan_left_mul_mem
    {R : Type*} [Semiring R] {A : Type*} [NonUnitalNonAssocRing A]
    [IsLeibniz A] [Module R A] [SMulCommClass R A A] (a : A) :
    map (LinearMap.mulLeft R a) (spanOfSquares R A) ≤ spanOfSquares R A := by
  dsimp [spanOfSquares]
  rw [map_span_le (LinearMap.mulLeft R a) (Set.range fun x : A => x * x)
    (span R (Set.range fun x ↦ x * x))]
  intro x ⟨y, hy⟩
  simp only at hy
  simp only [LinearMap.mulLeft_apply]
  rw [← hy, mul_left_mul_self]
  apply zero_mem

/-- The span of squares is stable under right multiplication in a right Leibniz ring. -/
lemma squareSpan_right_mul_mem {R : Type*} [Ring R] {A : Type*}
      [NonUnitalNonAssocRing A] [IsLeibniz A] [Module R A] [IsScalarTower R A A] (a : A) :
    map (LinearMap.mulRight R a) (spanOfSquares R A) ≤
      spanOfSquares R A := by
  dsimp [spanOfSquares]
  rw [map_span_le (LinearMap.mulRight R a) (Set.range fun x : A => x * x)
    (span R (Set.range fun x ↦ x * x))]
  intro x ⟨y, hy⟩
  simp only at hy
  simp only [LinearMap.mulRight_apply]
  rw [← hy,Leibniz.leibniz y y a]
  exact symm_SpanOfSquares_mem (R := R) (y * a) y


end Leibniz

namespace NonUnitalNonAssocSemiring

/-- The condition that every element of a non-unital, non-associative semiring squares to zero.
For a unital ring, this condition forces `1 = 0`. -/
class IsSkew (A : Type*) [NonUnitalNonAssocSemiring A] where
  skew (x : A) : x * x = 0

end NonUnitalNonAssocSemiring

namespace Leibniz

open NonUnitalNonAssocSemiring

/-- A Leibniz ring in which every element squares to zero is a Lie ring,
with bracket given by multiplication. -/
instance instLieRing {A : Type*} [NonUnitalNonAssocRing A] [IsLeibniz A] [IsSkew A] :
    LieRing A := {
  bracket := fun x y ↦ x * y
  add_lie := add_mul
  lie_add := smul_add
  lie_self := IsSkew.skew
  leibniz_lie := by
    intro x y z
    rw [mul_left_mul]
    have : (y + x * z) * y + (y + x * z) * (x * z) = 0 := by
      rw [← mul_add]
      apply IsSkew.skew
    rw [← neg_eq_iff_add_eq_zero, add_mul, add_mul] at this
    simp only [IsSkew.skew, zero_add, add_zero] at this
    rw [sub_eq_add_neg, this]
}

/-- A Leibniz algebra in which every element squares to zero is a Lie algebra,
with bracket given by multiplication. -/
instance instLieAlgebra {R : Type*} [CommRing R] {A : Type*} [NonUnitalNonAssocRing A]
      [IsLeibniz A] [IsSkew A] [Module R A] [SMulCommClass R A A] :
    LieAlgebra R A := {
  lie_smul := by
    intro r x y
    change x * (r • y) = r • (x * y)
    rw [← smul_eq_mul, ← smul_eq_mul, ← smul_comm]
}

section OfLie

/-- A Lie ring satisfies the right Leibniz identity when its bracket is used as multiplication
via `LieRing.toNonUnitalNonAssocRing`. -/
instance ofLieRing {A : Type*} [LieRing A] : @IsLeibniz A (LieRing.toNonUnitalNonAssocRing A):= by
  let _ := LieRing.toNonUnitalNonAssocRing A
  exact {
  leibniz' := by
    intro x y z
    change ⁅⁅x, y⁆, z⁆ = ⁅⁅x, z⁆, y⁆ + ⁅x, ⁅y, z⁆⁆
    rw [lie_lie,add_comm]
    refine sub_eq_iff_eq_add.mpr ?_
    abel_nf
    refine left_eq_add.mpr ?_
    rw [← lie_skew]
    module }

end OfLie

end Leibniz


/- --------------------------QUOTIENTS and IDEALS -------------------- -/

namespace Leibniz

open Submodule

open NonUnitalNonAssocAlgebra
open NonUnitalNonAssocSemiring

/-- The Leibniz ideal in a Leibniz algebra is the ideal spanned by squares. -/
def leibnizIdeal (R : Type*) [Ring R] (A : Type*) [NonUnitalNonAssocRing A]
    [IsLeibniz A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] :
    TwoSidedIdeal R A :=
  { spanOfSquares R A with
    left_mul_mem' a x hx := by
      rw [← LinearMap.mulLeft_apply R]
      apply squareSpan_left_mul_mem
      exact mem_map_of_mem (f:=(LinearMap.mulLeft R a)) hx
    right_mul_mem' a x hx := by
      rw [← LinearMap.mulRight_apply R]
      apply squareSpan_right_mul_mem
      apply mem_map_of_mem hx
  }

instance (R : Type*) [Ring R] (A : Type*) [NonUnitalNonAssocRing A]
      [IsLeibniz A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
      : AddCommGroup (leibnizIdeal R A) :=
  inferInstanceAs <| AddCommGroup ((leibnizIdeal R A).toSubmodule)

instance (R : Type*) [Ring R] (A : Type*) [NonUnitalNonAssocRing A]
      [IsLeibniz A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
      : Module R (leibnizIdeal R A) :=
  inferInstanceAs <| Module R ((leibnizIdeal R A).toSubmodule)

theorem leibnizIdeal_toSubmodule {R : Type*} [Ring R] {A : Type*}
      [NonUnitalNonAssocRing A] [IsLeibniz A] [Module R A]
      [SMulCommClass R A A] [IsScalarTower R A A] :
    (leibnizIdeal R A).toSubmodule = span R (Set.range fun x : A => x * x) := by
  rfl

theorem square_mem_leibnizIdeal (R : Type*) [Ring R] {A : Type*}
      [NonUnitalNonAssocRing A] [IsLeibniz A] [Module R A]
      [SMulCommClass R A A] [IsScalarTower R A A] (x : A) :
    x * x ∈ leibnizIdeal R A := by
  rw [← TwoSidedIdeal.mem_toSubmodule, leibnizIdeal_toSubmodule]
  apply subset_span
  simp

/-- An ideal contains the Leibniz ideal if and only if it contains every square. -/
theorem leibnizIdeal_le_iff (R : Type*) [Ring R] (A : Type*) [NonUnitalNonAssocRing A]
    [IsLeibniz A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
    {I : TwoSidedIdeal R A} :
    leibnizIdeal R A ≤ I ↔ ∀ x : A, x * x ∈ I := by
  constructor
  · intro hI x
    refine Set.mem_of_mem_of_subset ?_ hI
    apply square_mem_leibnizIdeal
  · intro hx
    apply span_le.mpr
    intro y ⟨z,hy⟩
    apply hx at z
    rw [← hy]
    simpa

namespace Quotient

open NonUnitalNonAssocAlgebra

variable (R : Type*) [Ring R]
variable (A : Type*) [NonUnitalNonAssocRing A] [IsLeibniz A]
variable [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]

instance {I : TwoSidedIdeal R A} : IsLeibniz (A ⧸ I) := {
  leibniz' x y z := by
    apply TwoSidedIdeal.Quotient.induction_on x
    intro x
    apply TwoSidedIdeal.Quotient.induction_on y
    intro y
    apply TwoSidedIdeal.Quotient.induction_on z
    intro z
    simp only [← TwoSidedIdeal.Quotient.mk_mul, ← TwoSidedIdeal.Quotient.mk_add]
    rw [Leibniz.leibniz]
}

instance {R : Type*} [Ring R] {A : Type*}
      [NonUnitalNonAssocRing A] [IsLeibniz A] [Module R A]
      [SMulCommClass R A A] [IsScalarTower R A A] :
    IsSkew (A ⧸ leibnizIdeal R A) := by
  constructor
  intro x
  apply TwoSidedIdeal.Quotient.induction_on x
  intro x
  rw [← TwoSidedIdeal.Quotient.mk_mul, TwoSidedIdeal.Quotient.mk_eq_zero]
  apply square_mem_leibnizIdeal

/-- The Leibniz quotient `A ⧸ leibnizIdeal R A` is a Lie algebra. -/
instance {R : Type*} [CommRing R] {A : Type*}
      [NonUnitalNonAssocRing A] [IsLeibniz A] [Module R A]
      [SMulCommClass R A A] [IsScalarTower R A A] :
    LieAlgebra R (A ⧸ leibnizIdeal R A) := by
  exact Leibniz.instLieAlgebra

/-- Every element of the quotient squares to zero if and only if
the defining ideal contains the Leibniz ideal. -/
theorem isSkew_quotient_iff {I : TwoSidedIdeal R A} :
    IsSkew (A ⧸ I) ↔ leibnizIdeal R A ≤ I := by
  constructor
  · intro hSk
    apply (leibnizIdeal_le_iff (R:=R) (A:=A) (I:=I)).mpr
    intro x
    apply (TwoSidedIdeal.Quotient.mk_eq_zero).mp
    rw [TwoSidedIdeal.Quotient.mk_mul]
    apply IsSkew.skew
  · rw [leibnizIdeal_le_iff]
    intro h
    refine { skew := ?_ }
    intro x
    have ⟨ a,ha⟩:=Quotient.mk''_surjective x
    rw [← ha]
    change TwoSidedIdeal.Quotient.mk (R:=R) (I:=I) a * TwoSidedIdeal.Quotient.mk (R:=R) (I:=I) a = 0
    rw [← TwoSidedIdeal.Quotient.mk_mul]
    apply (TwoSidedIdeal.Quotient.mk_eq_zero).mpr
    exact h a

end Quotient

variable {R : Type*} [Ring R]
variable {A : Type*} [NonUnitalNonAssocRing A]
variable [Module R A] [SMulCommClass R A A]
variable [IsLeibniz A]

variable (R A) in
/-- The right annihilator `{x | y * x = 0 for all y}` is an ideal in a Leibniz algebra. -/
def rightAnnihilator : TwoSidedIdeal R A where
  carrier := {x : A | ∀ y : A, y * x = 0}
  zero_mem' := by intro y; simp
  add_mem' := by
    intro x y hx hy z
    rw [mul_add, hx z, hy z, zero_add]
  smul_mem' := by
    intro r x hx y
    rw [mul_smul_comm, hx y, smul_zero]
  left_mul_mem' a {x} hx := by
    change ∀ y : A, y * (a * x) = 0
    change ∀ y : A, y * x = 0 at hx
    intro y
    have h := leibniz (y) (a) (x)
    rw [hx (y * a), hx y] at h
    simpa using h.symm
  right_mul_mem' a {x} hx := by
    change ∀ y : A, y * (x * a) = 0
    change ∀ y : A, y * x = 0 at hx
    intro y
    have h := leibniz (y) (x) (a)
    rw [hx y, hx (y * a)] at h
    simpa using h.symm

instance : AddCommGroup (rightAnnihilator R A) :=
  inferInstanceAs <| AddCommGroup ((rightAnnihilator R A).toSubmodule)

instance : Module R (rightAnnihilator R A) :=
  inferInstanceAs <| Module R ((rightAnnihilator R A).toSubmodule)

@[simp]
theorem mem_rightAnnihilator {x : A} :
    x ∈ rightAnnihilator R A ↔ ∀ y : A, y * x = 0 :=
  Iff.rfl

theorem square_mem_rightAnnihilator (x : A) : x * x ∈ rightAnnihilator R A  := by
  dsimp [rightAnnihilator]
  intro y
  exact mul_left_mul_self x y

theorem rightAnnihilator_eq_top_iff :
    rightAnnihilator R A = ⊤ ↔ ∀ x y : A, x * y = 0 := by
  simp_rw [← Function.Injective.eq_iff TwoSidedIdeal.toSubmodule_injective,
    TwoSidedIdeal.top_toSubmodule, eq_top_iff', TwoSidedIdeal.mem_toSubmodule,
    mem_rightAnnihilator]
  rw [forall_comm]

/-- If `rightAnnihilator R A = ⊤`, then every element of `A` squares to zero. -/
theorem isSkew_of_rightAnnihilator_eq_top (h : rightAnnihilator R A = ⊤) :
    IsSkew A := by
  refine { skew := ?_ }
  rw [rightAnnihilator_eq_top_iff (R:=R) (A:=A)] at h
  intro x
  exact h x x

/-- If `rightAnnihilator R A = ⊥`, then every element of `A` squares to zero. -/
theorem square_eq_zero_of_rightAnnihilator_eq_bot (h : rightAnnihilator R A = ⊥) :
    IsSkew A := by
  refine {skew :=?_ }
  simp_rw [← Function.Injective.eq_iff TwoSidedIdeal.toSubmodule_injective,
    TwoSidedIdeal.bot_toSubmodule, Submodule.eq_bot_iff, TwoSidedIdeal.mem_toSubmodule,
    mem_rightAnnihilator] at h
  intro x
  apply h
  apply mul_left_mul_self

variable [IsScalarTower R A A]

theorem leibnizIdeal_in_rightAnnihilator :
    leibnizIdeal R A ≤ rightAnnihilator R A := by
  unfold leibnizIdeal
  unfold spanOfSquares
  apply (Submodule.span_le).mpr
  intro x hx
  rw [Set.mem_range] at hx
  obtain ⟨y, hy⟩ := hx
  unfold rightAnnihilator
  simp only [coe_set_mk, AddSubmonoid.coe_set_mk, AddSubsemigroup.coe_set_mk, Set.mem_ofPred_eq]
  intro z
  rw [← hy]
  exact mul_left_mul_self y z

variable (R) in
theorem leibnizideal_eq_bot_iff : leibnizIdeal R A = ⊥ ↔ IsSkew A := by
  rw [← Function.Injective.eq_iff TwoSidedIdeal.toSubmodule_injective,
    TwoSidedIdeal.bot_toSubmodule, Submodule.eq_bot_iff, leibnizIdeal_toSubmodule]
  constructor
  · intro h
    refine { skew := ?_ }
    intro x
    specialize h (x * x)
    apply h
    apply Submodule.subset_span
    use x
  · intro _ _ hx
    have : Set.range (fun (x : A) ↦ x * x) = { 0 } := by
      rw [Set.range_eq_singleton_iff]
      exact fun x ↦ IsSkew.skew x
    rw [this] at hx
    simp only [span_zero_singleton, mem_bot] at hx
    exact hx

variable (R) in
/-- `leibnizIdeal R A = ⊥` if and only if every element of `A` squares to zero. -/
theorem leibnizideal_eq_bot_iff' : leibnizIdeal R A = ⊥ ↔ IsSkew A:= by
  rw [leibnizideal_eq_bot_iff R]

theorem leibnizIdeal_le_top_of_Nontrivial [Nontrivial A] :
    leibnizIdeal R A < ⊤ := by
  by_contra htop
  simp only [not_lt_top_iff] at htop
  have hRA : rightAnnihilator R A = ⊤ := by
    apply le_antisymm
    · exact le_top
    · rw [← htop]
      exact leibnizIdeal_in_rightAnnihilator (R:=R) (A:=A)
  have hskew :IsSkew A :=
    isSkew_of_rightAnnihilator_eq_top (R:=R) (A:=A) hRA
  have hbot : leibnizIdeal R A = ⊥ :=
    (leibnizideal_eq_bot_iff (R:=R) (A:=A)).mpr hskew
  have htopbot : (⊤ : NonUnitalNonAssocAlgebra.TwoSidedIdeal R A) = ⊥ :=
    htop.symm.trans hbot
  have hsub : Subsingleton A := by
    refine ⟨?_⟩
    intro x y
    have hx : x ∈ (⊤ : NonUnitalNonAssocAlgebra.TwoSidedIdeal R A) := mem_top
    rw [htopbot] at hx
    have hy : y ∈ (⊤ : NonUnitalNonAssocAlgebra.TwoSidedIdeal R A) := mem_top
    rw [htopbot] at hy
    have hx0 : x = 0 := (Submodule.mem_bot R).mp hx
    have hy0 : y = 0 := (Submodule.mem_bot R).mp hy
    exact hx0.trans hy0.symm
  exact (not_nontrivial_iff_subsingleton.mpr hsub) (inferInstance : Nontrivial A)

end Leibniz
