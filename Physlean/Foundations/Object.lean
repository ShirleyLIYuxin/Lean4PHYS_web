import Mathlib
-- PhysicsTheorems/Object.lean
structure SimObject where
  mass     : Float
  position : Float × Float × Float
  velocity : Float × Float × Float
  deriving Repr

structure TheoryObject where
  mass     : ℝ
  position : ℝ × ℝ × ℝ
  velocity : ℝ × ℝ × ℝ
