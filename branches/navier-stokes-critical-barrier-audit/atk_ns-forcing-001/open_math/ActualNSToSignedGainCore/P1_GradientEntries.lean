import open_math.ActualNSToSignedGainCore.P1_ConcreteObservables

/-!
NS-FORCING-001 / finite-dimensional gradient entry reconstruction.

Pure linear algebra for the concrete R3 velocity gradient.  This file contains
no analytic closure assumption and no proof gap.
-/

noncomputable section

open scoped BigOperators

namespace NSProducerFirst.P1Concrete

/-- Scalar matrix entry d_j u_i of the concrete spatial derivative. -/
def gradientEntry
    (u : VelocityField) (t : ℝ) (j i : Fin 3) (x : Space) : ℝ :=
  derivativeEntry j i (spatialDerivative u t x)

@[simp] theorem gradientEntry_apply
    (u : VelocityField) (t : ℝ) (j i : Fin 3) (x : Space) :
    gradientEntry u t j i x =
      (spatialDerivative u t x (coordinateVector j)) i := by
  rfl

/-- Coordinate decomposition of a vector in physical R3. -/
theorem coordinate_decomposition (v : Space) :
    ∑ j : Fin 3, v j • coordinateVector j = v := by
  classical
  classical
  ext i
  simp [coordinateVector, Finset.sum_apply, Pi.smul_apply,
    EuclideanSpace.single_apply]

/-- The operator norm of a linear map is bounded by the sum of the norms of
its three coordinate columns. -/
theorem opNorm_le_sum_coordinate_columns
    (A : Space →L[ℝ] Space) :
    ‖A‖ ≤ ∑ j : Fin 3, ‖A (coordinateVector j)‖ := by
  apply A.opNorm_le_bound
  · exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  intro v
  calc
    ‖A v‖ = ‖A (∑ j : Fin 3, v j • coordinateVector j)‖ := by
      rw [coordinate_decomposition]
    _ = ‖∑ j : Fin 3, v j • A (coordinateVector j)‖ := by
      simp only [map_sum, map_smul]
    _ ≤ ∑ j : Fin 3, ‖v j • A (coordinateVector j)‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin 3, ‖v‖ * ‖A (coordinateVector j)‖ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right
        (PiLp.norm_apply_le v j) (norm_nonneg _)
    _ = (∑ j : Fin 3, ‖A (coordinateVector j)‖) * ‖v‖ := by
      rw [← Finset.mul_sum, mul_comm]

/-- Each column norm is bounded by the sum of the absolute values of its
three scalar entries. -/
theorem column_norm_le_sum_entries
    (A : Space →L[ℝ] Space) (j : Fin 3) :
    ‖A (coordinateVector j)‖ ≤
      ∑ i : Fin 3, |(A (coordinateVector j)) i| := by
  classical
  calc
    ‖A (coordinateVector j)‖ =
        ‖∑ i : Fin 3,
          (A (coordinateVector j)) i • coordinateVector i‖ := by
      rw [coordinate_decomposition]
    _ ≤ ∑ i : Fin 3,
          ‖(A (coordinateVector j)) i • coordinateVector i‖ :=
      norm_sum_le _ _
    _ = ∑ i : Fin 3, |(A (coordinateVector j)) i| := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [coordinateVector, EuclideanSpace.norm_single, Real.norm_eq_abs]

/-- Pointwise reconstruction: the concrete operator norm of grad u is
controlled by the sum of its nine scalar matrix entries. -/
theorem spatialDerivative_norm_le_sum_entries
    (u : VelocityField) (t : ℝ) (x : Space) :
    ‖spatialDerivative u t x‖ ≤
      ∑ j : Fin 3, ∑ i : Fin 3, |gradientEntry u t j i x| := by
  calc
    ‖spatialDerivative u t x‖
        ≤ ∑ j : Fin 3,
            ‖spatialDerivative u t x (coordinateVector j)‖ :=
      opNorm_le_sum_coordinate_columns (spatialDerivative u t x)
    _ ≤ ∑ j : Fin 3, ∑ i : Fin 3,
          |gradientEntry u t j i x| := by
      apply Finset.sum_le_sum
      intro j hj
      simpa [gradientEntry] using
        column_norm_le_sum_entries (spatialDerivative u t x) j

#print axioms NSProducerFirst.P1Concrete.spatialDerivative_norm_le_sum_entries

end NSProducerFirst.P1Concrete
