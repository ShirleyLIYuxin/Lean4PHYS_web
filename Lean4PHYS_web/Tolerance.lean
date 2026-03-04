-- Tolerance.lean

-- Function to check if derived value is within 1% of the ground truth
def withinOnePercent (groundTruth derived : Float) : Bool :=
  let tolerance := 0.01 * groundTruth
  let lower := groundTruth - tolerance
  let upper := groundTruth + tolerance
  lower ≤ derived && derived ≤ upper

-- Generalized version for arbitrary percent tolerance
def withinPercent (percent : Float) (groundTruth derived : Float) : Bool :=
  let tolerance := (percent / 100.0) * groundTruth
  let lower := groundTruth - tolerance
  let upper := groundTruth + tolerance
  lower ≤ derived && derived ≤ upper

-- -- Some test cases
-- #eval withinOnePercent 100.0 100.5   -- false
-- #eval withinOnePercent 100.0 100.99  -- true
-- #eval withinOnePercent 100.0 98.99   -- false

-- #eval withinPercent 5.0 100.0 104.0  -- true
-- #eval withinPercent 5.0 100.0 95.0   -- true
-- #eval withinPercent 5.0 100.0 94.9   -- false
