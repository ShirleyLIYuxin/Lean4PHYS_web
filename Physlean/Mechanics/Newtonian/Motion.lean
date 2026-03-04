/-
  PhysLean.Mechanics.Newtonian.Motion

  General 1D Newtonian motion under a given force law.
  Defines motion models, solution predicates, and core theorems.
-/

/-
  PhysLean.Mechanics.Newtonian.Motion

  General 1D Newtonian motion under a given force law.
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Data.Real.Basic

namespace Physlean.Mechanics.Newtonian

open Real

/-- A 1D Newtonian motion model with mass `m` and force `F(v)` acting on the particle. -/
structure MotionModel where
  mass : ℝ
  force : ℝ → ℝ
  h_mass : 0 < mass

variable {M : MotionModel}

/-- The ODE: dv/dt = F(v)/m --/
noncomputable def accelerationODE (M : MotionModel) : ℝ → ℝ → ℝ :=
  fun _ v => M.force v / M.mass

/-- A velocity function `v(t)` satisfies Newton's second law for this model. -/
def IsVelSolution (M : MotionModel) (v : ℝ → ℝ) : Prop :=
  ∀ t, HasDerivAt v t (accelerationODE M t (v t))

/-- A position function `x(t)` corresponds to a velocity function `v(t)`. -/
def IsPosSolution (M : MotionModel) (x : ℝ → ℝ) : Prop :=
  ∃ v, IsVelSolution M v ∧ ∀ t, HasDerivAt x t (v t)

end Physlean.Mechanics.Newtonian
