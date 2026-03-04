/-
  PhysLean.Mechanics.Newtonian.Drag

  General and specific models of drag forces for Newtonian motion.
-/

import Physlean.Mechanics.Newtonian.Motion

namespace Physlean.Mechanics.Newtonian

/--
  A drag force proportional to v^n (power-law drag).
  The force is always opposite in direction to motion.
-/
def dragForce (k : ℝ) (n : ℕ) : ℝ → ℝ :=
  λ v => -k * v^n

/--
  Motion model under drag force proportional to v^n.
  Input: mass m > 0, drag coefficient k > 0, exponent n ≥ 1.
-/
def dragModel (m k : ℝ) (n : ℕ) (hm : 0 < m) (_hk : 0 < k) : MotionModel :=
  MotionModel.mk m (dragForce k n) hm

/-- Special case: cubic drag model where F = -k * v^3 -/
def cubicDragModel (m k : ℝ) (hm : 0 < m) (hk : 0 < k) : MotionModel :=
  dragModel m k 3 hm hk

end Physlean.Mechanics.Newtonian
