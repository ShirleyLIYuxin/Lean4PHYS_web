import Physlean.physlean_import
open scoped BigOperators Real InnerProductSpace

namespace PhysLean.Mechanics

/-- A vector in ℝⁿ represented as a function from `Fin n` to `ℝ`. -/
abbrev Vec (n : ℕ) := Fin n → ℝ
/-- A vector in ℚⁿ represented as a function from `Fin n` to `ℚ`. -/
abbrev QVec (n : ℕ) := Fin n → ℚ
/-- Dot product of two vectors in ℝⁿ. -/
def dot {n : ℕ} (v w : Vec n) : ℝ :=
  ∑ i, v i * w i

/-- Notation for dot product. -/
notation "⟪" v ", " w "⟫" => dot v w

abbrev Time := ℝ
abbrev Position (n : ℕ) := Time → Vec n

/-- Velocity is the componentwise derivative of position. -/
noncomputable def velocity {n : ℕ} (x : Position n) : Time → Vec n :=
  fun t i ↦ deriv (fun t ↦ x t i) t

/-- Acceleration is the second derivative of position. -/
noncomputable def acceleration {n : ℕ} (x : Position n) : Time → Vec n :=
  fun t i ↦ deriv (fun t ↦ deriv (fun t ↦ x t i) t) t

/-- Momentum is mass times velocity. -/
def momentum {n : ℕ} (m : ℝ) (v : Vec n) : Vec n :=
  fun i ↦ m * v i

/-- Kinetic energy is (1/2) * m * ‖v‖² using the inner product norm. -/
noncomputable def kineticEnergy {n : ℕ} (m : ℝ) (v : Vec n) : ℝ :=
  (1 / 2) * m * ‖v‖^2

/-- Work is the inner product of force and displacement. -/
def work {n : ℕ} (F d : Vec n) : ℝ :=
  ⟪F, d⟫

/-- Power is work divided by time interval. -/
noncomputable def power (W Δt : ℝ) : ℝ :=
  W / Δt

/-- Gravitational potential energy is m * g * h. -/
def gravitationalPotentialEnergy (m g h : ℝ) : ℝ :=
  m * g * h

end PhysLean.Mechanics
