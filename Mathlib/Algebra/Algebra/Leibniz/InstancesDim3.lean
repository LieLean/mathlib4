import Mathlib.Algebra.Algebra.Leibniz.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Logic.Equiv.Fin.Basic



/-! In this file we set the instances of isomorphism classes of Leibniz algberas of
    dimenison 3. -/

namespace Leibniz

namespace Dim3

variable {R : Type*} [Field R]

/- The Leibniz algebras are parametrized by  α₁ α₂ α₃ α₄ β₁ β₂ β₃ γ₁ μ δ ν -/
/- Cases 1 have vanishing `μ δ` and `ν = -β₂`.-/

def Families (_ _ _ _ _ _ _ _ _ _ _ : R) := Fin 3 → R

instance (α₁ α₂ α₃ α₄ β₁ β₂ β₃ γ₁ μ δ ν : R) : AddCommGroup (Families α₁ α₂ α₃ α₄ β₁ β₂ β₃ γ₁ μ δ ν)
  := inferInstanceAs <| AddCommGroup (Fin 3 → R)

/- The Leibniz product is obtained from the following identities in the canonical basis elements-/
/- `e₀ * e₁ = α₁ e₀ ; e₀ * e₂ = α₃ e₀ + μ e₁ ; e₁ * e₁ = α₂ e₀ ; e₂ * e₂ = α₄ e₀ + δ e₁ `-/
/- `e₂ * e₁ = β₁ e₀ + β₂ e₁ + β₃ e₂ ; e₁ * e₂ = γ₁ e₀ + ν e₁ - β₃ e₂ ; ∀ i, ei * e₀ = 0.`-/
instance (α₁ α₂ α₃ α₄ β₁ β₂ β₃ γ₁ μ δ ν : R) : Mul (Families α₁ α₂ α₃ α₄ β₁ β₂ β₃ γ₁ μ δ ν) := {
  mul x y := ![α₁ * x 0 * y 1 + α₃ * x 0 * y 2 + α₂ * x 1 * y 1 + γ₁ * x 1 * y 2 + β₁ * x 2 * y 1
    + α₄ * x 2 * y 2 , β₂ * x 2 * y 1 + ν  * x 1 * y 2 + μ * x 0 * y 2 + δ * x 2 * y 2,
      β₃ * x 2 * y 1 - β₃ * x 1 * y 2 ]
}

@[simp]
lemma Families.add_apply {α₁ α₂ α₃ α₄ β₁ β₂ β₃ γ₁ μ δ ν : R}
    (x y : Families α₁ α₂ α₃ α₄ β₁ β₂ β₃ γ₁ μ δ ν) (i : Fin 3) :
    (x + y) i = x i + y i := rfl

@[simp]
lemma Families.zero_apply {α₁ α₂ α₃ α₄ β₁ β₂ β₃ γ₁ μ δ ν : R} (i : Fin 3) :
    (0 : Families α₁ α₂ α₃ α₄ β₁ β₂ β₃ γ₁ μ δ ν) i = 0 := rfl

@[simp]
lemma Families.mul_def {α₁ α₂ α₃ α₄ β₁ β₂ β₃ γ₁ μ δ ν : R}
    (x y : Families α₁ α₂ α₃ α₄ β₁ β₂ β₃ γ₁ μ δ ν) :
    x * y = ![α₁ * x 0 * y 1 + α₃ * x 0 * y 2 + α₂ * x 1 * y 1 + γ₁ * x 1 * y 2 + β₁ * x 2 * y 1
    + α₄ * x 2 * y 2 , β₂ * x 2 * y 1 + ν  * x 1 * y 2 + μ * x 0 * y 2 + δ * x 2 * y 2,
      β₃ * x 2 * y 1 - β₃ * x 1 * y 2] := rfl

instance (α₁ α₂ α₃ α₄ β₁ β₂ β₃ γ₁ μ δ ν : R) :
    NonUnitalNonAssocRing (Families α₁ α₂ α₃ α₄ β₁ β₂ β₃ γ₁ μ δ ν)
  where
    toAddCommGroup := inferInstance
    left_distrib := by
      intro a b c
      funext i
      simp only [Families.add_apply]
      fin_cases i <;> simp <;> ring
    right_distrib := by
      intro a b c
      funext i
      simp only [Families.add_apply]
      fin_cases i <;> simp <;> ring
    zero_mul := by
      intro a
      funext i
      fin_cases i <;> simp
    mul_zero := by
      intro a
      funext i
      fin_cases i <;> simp

instance (α₁ α₂ α₃ α₄ β₁ β₂ β₃ γ₁ μ δ ν : R) : Module R (Families α₁ α₂ α₃ α₄ β₁ β₂ β₃ γ₁ μ δ ν) :=
  inferInstanceAs <| Module R (Fin 3 → R)

@[simp]
lemma Families.smul_apply {r : R} {α₁ α₂ α₃ α₄ β₁ β₂ β₃ γ₁ μ δ ν : R}
    (x : Families α₁ α₂ α₃ α₄ β₁ β₂ β₃ γ₁ μ δ ν) (i : Fin 3) :
    (r • x) i = r * x i := rfl

instance (α₁ α₂ α₃ α₄ β₁ β₂ β₃ γ₁ μ δ ν : R) :
    SMulCommClass R R (Families α₁ α₂ α₃ α₄ β₁ β₂ β₃ γ₁ μ δ ν)
  where
    smul_comm:= by
      intro m n x
      funext i
      simp [Families.smul_apply]
      ring

instance (α₁ α₂ α₃ α₄ β₁ β₂ β₃ γ₁ μ δ ν : R) :
   IsScalarTower R (Families α₁ α₂ α₃ α₄ β₁ β₂ β₃ γ₁ μ δ ν)
      (Families α₁ α₂ α₃ α₄ β₁ β₂ β₃ γ₁ μ δ ν) := {
  smul_assoc := by
    intro r x z
    funext i
    fin_cases i <;> try simp only [Fin.zero_eta, Fin.isValue, smul_eq_mul, Families.mul_def,
      Nat.succ_eq_add_one, Nat.reduceAdd, Families.smul_apply, Matrix.cons_val_zero]
    · change _ = r * (α₁ * x 0 * z 1 + α₃ * x 0 * z 2 + α₂ * x 1 * z 1 + γ₁ * x 1 * z 2
        + β₁ * x 2 * z 1 + α₄ * x 2 * z 2)
      ring
    · simp only [Fin.isValue, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      change _= r * (β₂ * x 2 * z 1 + ν * x 1 * z 2 + μ * x 0 * z 2 + δ * x 2 * z 2)
      ring
    · simp only [Fin.isValue, Fin.reduceFinMk, Matrix.cons_val]
      change _ = r * (β₃ * x 2 * z 1 - β₃ * x 1 * z 2)
      ring
}

section inductiveTypes

variable (R : Type) [Field R]

inductive Index where
  | L1 /-Case 1.1.1-/
  | L2 : (α : Rˣ) → Index /-Case 1.1.2 `α₃ ≠ 0`-/
  | L3 /-Case 1.1.2 `α₃ = 0`-/
  | L4 /-Case 1.2.1.1.A. Assumes `R² = R`-/
  | L5 : (α : Rˣ) → Index /-Case 1.2.1.1.B. Appears only in the case `R² ≠ R`-/
  | L6 : (α : Rˣ) → Index /-Case 1.2.1.2.-/
  | L7 /-Case 2.1.1 --> IT CAN ALSO BE WRITTEN AS A LEIBNIZ OF CASE 1 ???-/
  | L8 /-Case 2.2.1.1.A. Assumes `R² = R`.-/
  | L9 : (α : Rˣ) → Index /-Case 2.2.1.1.B. Assumes `R² ≠ R`.-/
  | L10 : (α : Rˣ) → Index /-Case 2.2.1.1.B. Assumes `R² ≠ R` and `γ₁ ≠ 0`.-/
  | L11 /-Case 2.2.1.2.-/
  | L12 /-Case 2.2.2.1.-/
  | L13 /-Case 2.2.2.2.-/

/- If it was a `def`, then a `show ... from` is needed in `IsLeibniz` instances-/
abbrev d (idx : Index R) : Type := --Fin 3 → R/-
  match idx with
  | .L1 => Families (0 : R) 1 (-2) 0 0 1 0 0 0 0 (-1)
  | .L2 α => Families (0 : R) 0 α 0 0 1 0 0 0 0 (-1)
  | .L3 => Families (0 : R) 0 0 1 0 1 0 0 0 0 (-1)
  | .L4 => Families (0 : R) 1 0 1 0 0 0 0 0 0 0
  | .L5 α => Families (0 : R) 1 0 α 0 0 0 0 0 0 0
  | .L6 α => Families (0 : R) 1 0 α 0 0 0 1 0 0 0
  | .L7 => Families (0 : R) 0 0 0 0 0 0 1 0 0 0
  | .L8 => Families (0 : R) 0 0 0 0 0 0 1 1 0 0
  | .L9 α => Families (0 : R) 0 0 0 0 0 0 α 1 0 0
  | .L10 α => Families (0 : R) 0 0 0 0 0 0 α 0 1 0
  | .L11 => Families (0 : R) 0 1 0 0 0 0 0 0 0 1
  | .L12 => Families (0 : R) 0 0 1 0 0 0 0 1 0 0
  | .L13 => Families (0 : R) 0 1 1 0 0 0 0 1 0 0

#check Index.L1

instance (idx : Index R) : NonUnitalNonAssocRing (d R idx) :=  by cases idx <;> infer_instance

instance (idx : Index R) : Module R (d R idx) := by cases idx <;> infer_instance

end inductiveTypes

namespace Families

variable (R : Type) [Field R]

variable {α₁ α₂ α₃ α₄ β₁ β₂ β₃ γ₁ μ δ ν : R} (x : Families α₁ α₂ α₃ α₄ β₁ β₂ β₃ γ₁ μ δ ν) (i : Fin 3)

/-- The coordinate map `toCoordinates` as an `R`-linear map. -/
def toCoordinates :
    (Families α₁ α₂ α₃ α₄ β₁ β₂ β₃ γ₁ μ δ ν) →ₗ[R] (Fin 3 → R) where
  toFun := fun x => x
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl

instance : CoeFun (Families α₁ α₂ α₃ α₄ β₁ β₂ β₃ γ₁ μ δ ν) (fun _ => Fin 3 → R) where
  coe := toCoordinates R

#check toCoordinates R x i

lemma toCoordinates_apply : toCoordinates R x = x
    := rfl

lemma toCoordinates_injective : Function.Injective (@toCoordinates R _ α₁ α₂ α₃ α₄ β₁ β₂ β₃ γ₁ μ δ ν)
    := by
  intro x y hxy
  exact hxy

omit [Field R] in
@[ext]
lemma ext {x y : Families α₁ α₂ α₃ α₄ β₁ β₂ β₃ γ₁ μ δ ν}
    (h0 : x 0 = y 0) (h1 : x 1 = y 1) (h2 : x 2 = y 2)
    : x = y := by
  funext i
  fin_cases i <;> assumption

end Families

namespace d

variable (R : Type) [Field R]

variable {R} in
/-- The coordinate map `toCoordinates` as an `R`-linear map. -/
def toCoordinates (idx : Index R) : d R idx →ₗ[R] (Fin 3 → R) where
  toFun := by
    cases idx <;> use @Families.toCoordinates R _ _ _ _ _ _ _ _ _ _ _ _
  map_add' := by
    intro x y
    cases idx <;> rfl
  map_smul' := by
    intro r x
    cases idx <;> rfl

variable {idx : Index R} (x : d R idx)
#check toCoordinates

instance {idx : Index R} :
    CoeFun (d R idx) (fun _ => Fin 3 → R) where
  coe := toCoordinates idx

lemma toCoordinates_injective {idx : Index R} : Function.Injective (@toCoordinates R _ idx) := by
  cases idx <;> unfold toCoordinates <;> exact Families.toCoordinates_injective R

lemma toCoordinates_mul_L1 (x y : d R .L1) :
    toCoordinates .L1 (x * y) = ![-2 * (toCoordinates .L1 x) 0 * (toCoordinates .L1 y) 2 +
    (toCoordinates .L1 x) 1 * (toCoordinates .L1 y) 1, (
    toCoordinates .L1 x) 2 * (toCoordinates .L1 y) 1 -
    (toCoordinates .L1 x) 1 * (toCoordinates .L1 y) 2, 0] := by
  change x * y = ![-2 * x 0 * y 2 + x 1 * y 1, x 2 * y 1 - x 1 * y 2, 0]
  rw [Families.mul_def]
  simp [sub_eq_add_neg]
  rfl

set_option trace.profiler true in
instance (idx : Index R) : IsLeibniz (d R idx) :=
  match idx with
  | .L1 => {
            leibniz' x y z := by
              apply toCoordinates_injective R (idx := .L1)
              rw [map_add]
              repeat rw [Families.mul_def]
              simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, zero_mul, neg_mul,
                zero_add, one_mul, add_zero, sub_self, Matrix.cons_val_zero, Matrix.cons_val_one,
                Matrix.cons_val, mul_zero, neg_add_rev, neg_neg]
              erw [Families.toCoordinates_apply R, Families.toCoordinates_apply R,
                Families.toCoordinates_apply R]
              ext i
              fin_cases i <;> simp <;> ring
              --also works after rw [map_add]: (but takes longer to elab)
              --the proof below makes use of d.toCoordinates_mul_L1,
              --repeat rw [toCoordinates_mul_L1]
              --funext i
              --fin_cases i <;> simp <;> ring

          }
  | _ => sorry
              /-
  | .L2 α => {
            leibniz' x y z := by
              funext i
              simp only [Families.add_apply]
              repeat rw [Families.mul_def]
              fin_cases i <;> simp <;> ring_nf}
  | .L3 => {
            leibniz' x y z := by
              funext i
              simp only [Families.add_apply]
              repeat rw [Families.mul_def]
              fin_cases i <;> simp; ring_nf}
  | .L4 => {
            leibniz' x y z := by
              funext i
              simp only [Families.add_apply, Families.mul_def]
              fin_cases i <;> simp}
  | .L5 α => {
            leibniz' x y z := by
              funext i
              simp only [Families.add_apply]
              repeat rw [Families.mul_def]
              fin_cases i <;> simp}
  | .L6 α => {
            leibniz' x y z := by
              funext i
              simp only [Families.add_apply]
              repeat rw [Families.mul_def]
              fin_cases i <;> simp}
  | .L7 => {
            leibniz' x y z := by
              funext i
              simp only [Families.add_apply]
              repeat rw [Families.mul_def]
              fin_cases i <;> simp}
  | .L8 => {
            leibniz' x y z := by
              funext i
              simp only [Families.add_apply]
              repeat rw [Families.mul_def]
              fin_cases i <;> simp <;> grind}
  | .L9 α => {
            leibniz' x y z := by
              funext i
              simp only [Families.add_apply]
              repeat rw [Families.mul_def]
              fin_cases i <;> simp <;> grind}
  | .L10 α => {
            leibniz' x y z := by
              funext i
              simp only [Families.add_apply]
              repeat rw [Families.mul_def]
              fin_cases i <;> simp; grind}
  | .L11 => {
            leibniz' x y z := by
              funext i
              simp only [Families.add_apply]
              repeat rw [Families.mul_def]
              fin_cases i <;> simp <;> grind}
  | .L12 => {
            leibniz' x y z := by
              funext i
              simp only [Families.add_apply]
              repeat rw [Families.mul_def]
              fin_cases i <;> simp; grind}
  | .L13 => {
            leibniz' x y z := by
              funext i
              simp only [Families.add_apply]
              repeat rw [Families.mul_def]
              fin_cases i <;> simp <;> grind} -/

variable (idx : Index R)

#synth NonUnitalNonAssocRing (d R idx)

#synth IsLeibniz (d R idx)


variable {A : Type*} [NonUnitalNonAssocRing A] [IsLeibniz A] [Module R A] [SMulCommClass R A A]
variable [IsScalarTower R A A]

theorem d_is_injective : ∀ idx idx', Nonempty (d R idx ≃ₙₐ[R] d R idx') → idx = idx' := by
  intro x y

  sorry


theorem classif (dim3 : Module.finrank R A = 3) : ∃! idx, Nonempty (d R idx ≃ₙₐ[R] A) := by
  sorry

end d
