import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Basic.SetLike.Basic
import Mathlib.Order.Notation
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Quotient
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.Tactic.Module

/-! Please insert a Head of doc -/

namespace NonUnitalNonAssocAlgebra


variable (R : Type*) [Semiring R]
variable (A : Type*) [NonUnitalNonAssocSemiring A]
variable [Module R A] --[SMulCommClass R A A] [IsScalarTower R A A]

structure TwoSidedIdeal extends Submodule R A where
  left_mul_mem' (a : A) {x : A} : x ∈ carrier → a * x ∈ carrier
  right_mul_mem' (a : A) {x : A} : x ∈ carrier → x * a ∈ carrier

instance : Coe (TwoSidedIdeal R A) (Submodule R A) where
  coe := TwoSidedIdeal.toSubmodule

attribute [coe] TwoSidedIdeal.toSubmodule

namespace TwoSidedIdeal

variable {R A}

instance : SetLike (TwoSidedIdeal R A) A where
  coe := fun I ↦ I.carrier
  coe_injective I J h := by
    cases I; cases J; congr;
    exact SetLike.coe_injective h

instance : PartialOrder (TwoSidedIdeal R A) := .ofSetLike (TwoSidedIdeal R A)

theorem left_mul_mem {I : TwoSidedIdeal R A} (a : A) (x : A) (hx : x ∈ I) : a * x ∈ I :=
  left_mul_mem' _ a hx

theorem right_mul_mem {I : TwoSidedIdeal R A} (a : A) (x : A) (hx : x ∈ I) : x * a ∈ I :=
  right_mul_mem' _ a hx

instance : Bot (TwoSidedIdeal R A) :=
⟨{ (⊥ : Submodule R A) with
  left_mul_mem' := by simp
  right_mul_mem' := by simp }⟩

instance : Top (TwoSidedIdeal R A) :=
  ⟨{ carrier := ⊤
     zero_mem' := by simp
     add_mem' := by simp
     smul_mem' := by simp
     left_mul_mem' := by simp
     right_mul_mem' := by simp }⟩

@[simp]
theorem mem_toSubmodule (I : TwoSidedIdeal R A) {x : A} :
    x ∈ I.toSubmodule ↔ x ∈ I :=
  Iff.rfl

@[simp]
theorem mem_top {x : A} :
    x ∈ (⊤ : TwoSidedIdeal R A) :=
  trivial

@[ext]
theorem ext {I J : TwoSidedIdeal R A} (h : ∀ x, x ∈ I ↔ x ∈ J) : I = J :=
  SetLike.ext h

@[simp]
theorem coe_toSubmodule (I : TwoSidedIdeal R A) : (toSubmodule I : Set A) = I := rfl

@[simp]
theorem bot_toSubmodule : (⊥ : TwoSidedIdeal R A).toSubmodule = ⊥ := rfl

@[simp]
theorem top_toSubmodule : (⊤ : TwoSidedIdeal R A).toSubmodule = ⊤ := rfl

@[simp]
theorem coe_top : ((⊤ : TwoSidedIdeal R A) : Set A) = Set.univ := rfl

instance : OrderTop (TwoSidedIdeal R A) where
  le_top _ _ _ := trivial

theorem toSubmodule_injective :
    Function.Injective (toSubmodule : TwoSidedIdeal R A → Submodule R A) := fun x y h ↦ by
  cases x; cases y; congr

variable {R : Type*} [Ring R]
variable {A : Type*} [NonUnitalNonAssocRing A]
variable [Module R A]

instance instHasQuotient :
    HasQuotient A (TwoSidedIdeal R A) :=
  ⟨fun I ↦ A ⧸ I.toSubmodule⟩

namespace Quotient

variable {I : TwoSidedIdeal R A}

def mk : A → A ⧸ I :=
  Quotient.mk''

theorem eq_submodule_quotient :
    (A ⧸ I) = (A ⧸ I.toSubmodule) :=
  rfl

instance : AddCommGroup (A ⧸ I) :=
  inferInstanceAs <| AddCommGroup (A ⧸ I.toSubmodule)

instance : Module R (A ⧸ I) :=
  inferInstanceAs <| Module R (A ⧸ I.toSubmodule)

instance : Mul (A ⧸ I) := {
  mul := Quotient.map₂' (fun x y : A ↦ x * y) (by
    simp_rw [Submodule.quotientRel_def, mem_toSubmodule]
    intro a₁ a₂ ha b₁ b₂ hb
    have : a₁ * b₁ - a₂ * b₂ = a₁ * (b₁ - b₂) + (a₁ - a₂) * b₂ := by
      rw [mul_sub, sub_mul]
      module
    rw [this]
    apply I.add_mem <;> rw [mem_toSubmodule]
    · exact left_mul_mem _ _ hb
    · exact right_mul_mem _ _ ha
  )
}

@[simp]
theorem mk_add {x y : A} : (mk (x + y) : A ⧸ I) = mk x + mk y :=
  rfl

@[simp]
theorem mk_neg {x : A} : (mk (-x) : A ⧸ I) = -(mk x) :=
  rfl

@[simp]
theorem mk_sub {x y : A} : (mk (x - y) : A ⧸ I) = mk x - mk y :=
  rfl

@[simp]
theorem mk_mul {x y : A} : (mk (x * y) : A ⧸ I) = mk x * mk y :=
  rfl

@[simp]
theorem mk_smul {r : R} {x : A} : (mk (r • x) : A ⧸ I) = r • mk x :=
  rfl

theorem eq {x y : A} : (mk x : A ⧸ I) = mk y ↔ x - y ∈ I :=
  Submodule.Quotient.eq I.toSubmodule

@[simp]
theorem mk_eq_zero {x : A} : (mk x : A ⧸ I) = 0 ↔ x ∈ I :=
  Submodule.Quotient.mk_eq_zero I.toSubmodule

@[simp]
theorem mk_zero : mk (0 : A)  = (0 : A ⧸ I) := by rfl

instance : NonUnitalNonAssocRing (A ⧸ I) := fast_instance%
  Function.Surjective.nonUnitalNonAssocRing (R := A) (S := A ⧸ I) _ Quotient.mk''_surjective rfl
  (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

theorem induction_on {C : A ⧸ I → Prop} (x : A ⧸ I) (H : ∀ z, C (mk z)) :
    C x := Quotient.inductionOn' x H

instance [SMulCommClass R A A] : SMulCommClass R (A ⧸ I) (A ⧸ I) := {
  smul_comm := by
    intro r x
    apply induction_on x
    intro x y
    apply induction_on y
    intro y
    simp only [smul_eq_mul, ← mk_mul, ← mk_smul]
    rw [← smul_eq_mul, ← smul_eq_mul, smul_comm]
}

instance [IsScalarTower R A A] : IsScalarTower R (A ⧸ I) (A ⧸ I) := {
  smul_assoc := by
    intro r x
    apply induction_on x
    intro x y
    apply induction_on y
    intro y
    simp only [smul_eq_mul, ← mk_mul, ← mk_smul]
    rw [← smul_eq_mul, ← smul_eq_mul, smul_assoc]
}

end Quotient
end TwoSidedIdeal
