import Physlean.physlean_import
import Physlean.Mechanics.Definitions
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace PhysLean.Mechanics.Statics

/-- A discrete system of `n` particles in `d`-dimensional space. -/
structure DiscreteSystem (n d : ℕ) where
  mass : Fin n → ℚ
  pos : Fin n → QVec d

/-- Total mass of a discrete system. -/
def DiscreteSystem.totalMass {n d : ℕ} (s : DiscreteSystem n d) : ℚ :=
  ∑ i, s.mass i

/--
Center of Mass for Discrete Mass Distribution.
The center of mass of a system of particles is the unique point in space where
the weighted relative position of the distributed mass sums to zero.

Mathematically, for a system of particles with positions `rᵢ : ℝᵈ` and masses `mᵢ : ℝ`,
the center of mass `R : ℝᵈ` is defined as: `R = (1 / M) ∑ mᵢ rᵢ`, where `M = ∑ᵢ mᵢ` is the total mass of the system.
-/

def DiscreteSystem.centerOfMass {n d : ℕ} (s : DiscreteSystem n d) : QVec d :=
  let M := s.totalMass
  if M ≠ 0 then
    fun j ↦ (∑ i, s.mass i * s.pos i j) / M
  else
    fun _ ↦ 0  -- center of mass is undefined for zero total mass; here defaulted to zero

-- def testSystemQ : DiscreteSystem 3 2 where
--   mass := ![2, 1, 3]
--   pos := ![![0, 0], ![1, 0], ![0, 2]]

-- #eval testSystemQ.centerOfMass 0  -- evaluates x-component
-- #eval testSystemQ.centerOfMass 1  -- evaluates y-component

/--
**Definition (Gravitational Force)**

The gravitational force is the downward force exerted on a mass by a gravitational field.
Near Earth's surface, it is approximated as:

`F = m ⋅ g`

where `m` is the mass and `g` is the gravitational acceleration vector.
-/
def gravitationalForce {n : ℕ} (m : ℝ) (g : Vec n) : Vec n :=
  fun i ↦ m * g i

/--
**Definition (Elastic or Spring Force)**

The elastic (restoring) force from a spring obeys Hooke's Law:

`F = -k ⋅ x`

where `k` is the spring constant and `x` is the displacement vector from equilibrium.
-/
def springForce {n : ℕ} (k : ℝ) (x : Vec n) : Vec n :=
  fun i ↦ -k * x i
/--
**Definition (Static Friction Force Bound)**

Static friction resists the initiation of sliding. It satisfies:

`‖F‖ ≤ μₛ ⋅ N`

where `μₛ` is the coefficient of static friction and `N` is the normal force magnitude.
This force adapts up to a maximum threshold.
-/
structure StaticFriction where
  μs : ℝ
  N  : ℝ

/--
**Definition (Kinetic Friction Force)**

Kinetic friction opposes the direction of motion and has magnitude:

`‖F‖ = μₖ ⋅ N`

where `μₖ` is the coefficient of kinetic friction and `N` is the normal force magnitude.
-/
noncomputable def kineticFrictionForce {n : ℕ} (μk N : ℝ) (v : Vec n) : Vec n :=
  let speed := ‖v‖
  if speed ≠ 0 then
    -- Direction opposite to velocity
    fun i ↦ -μk * N * (v i / speed)
  else
    fun _ ↦ 0

/--
**Definition (Rolling Friction Approximation)**

Rolling friction is usually small and approximated as:

`‖F‖ = μᵣ ⋅ N`

where `μᵣ` is the coefficient of rolling friction.
This force also opposes motion direction.
-/
noncomputable def rollingFrictionForce {n : ℕ} (μr N : ℝ) (v : Vec n) : Vec n :=
  let speed := ‖v‖
  if speed ≠ 0 then
    fun i ↦ -μr * N * (v i / speed)
  else
    fun _ ↦ 0


/-- A general force acting at a point in ℝⁿ, optionally with a point of application (for torque) -/
structure Force (n : ℕ) where
  vector : Vec n               -- the force vector
  point  : Option (Vec n) := none  -- point of application (used for torque analysis)

/-- A collection of forces acting on a body in ℝⁿ -/
structure ForceSystem (n : ℕ) where
  forces : List (Force n)

/-- Resultant force is the vector sum of all forces in the system -/
def resultantForce {n : ℕ} (sys : ForceSystem n) : Vec n :=
  sys.forces.foldl (fun acc f ↦ fun i ↦ acc i + f.vector i) (fun _ ↦ 0)
