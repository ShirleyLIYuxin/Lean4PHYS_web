
/-- A 3-dimensional real vector -/
structure Vec3 where
  x : Float
  y : Float
  z : Float
  deriving Repr

namespace Vec3

def approxEq (v₁ v₂ : Vec3) (ε : Float := 1e-6) : Bool :=
  Float.abs (v₁.x - v₂.x) < ε &&
  Float.abs (v₁.y - v₂.y) < ε &&
  Float.abs (v₁.z - v₂.z) < ε

/-- Vector addition -/
def add (u v : Vec3) : Vec3 :=
  ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩

/-- Vector subtraction -/
def sub (u v : Vec3) : Vec3 :=
  ⟨u.x - v.x, u.y - v.y, u.z - v.z⟩

/-- Scalar multiplication -/
def smul (a : Float) (v : Vec3) : Vec3 :=
  ⟨a * v.x, a * v.y, a * v.z⟩

/-- Dot product -/
def dot (u v : Vec3) : Float :=
  u.x * v.x + u.y * v.y + u.z * v.z

/-- Cross product -/
def cross (u v : Vec3) : Vec3 :=
  ⟨ u.y * v.z - u.z * v.y,
    u.z * v.x - u.x * v.z,
    u.x * v.y - u.y * v.x ⟩

/-- Magnitude (Euclidean norm) -/
def norm (v : Vec3) : Float :=
  Float.sqrt (v.x * v.x + v.y * v.y + v.z * v.z)

/-- Normalize a vector (unit vector in same direction) -/
def normalize (v : Vec3) : Vec3 :=
  let n := norm v
  if n == 0.0 then v else smul (1.0 / n) v

instance : ToString Vec3 where
  toString v := s!"({v.x}, {v.y}, {v.z})"

end Vec3
