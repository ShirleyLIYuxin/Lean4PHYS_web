import Mathlib.Data.Rat.Init

namespace PhysicsDefs

/--
A physical quantity with a rational value and a unit represented as a string.
-/
structure Quantity where
  val : ℚ
  unit : String
deriving Repr

/--
Computes averange acceleration given initial velocity `v₀`, final velocity `vₜ`, and time `t`.

Formula: a = (vₜ - v₀) / t
-/
def acceleration (v₀ vₜ t : ℚ) : ℚ :=
  (vₜ - v₀) / t

end PhysicsDefs


namespace Float

def pi : Float := 3.14159265358979323846

end Float
