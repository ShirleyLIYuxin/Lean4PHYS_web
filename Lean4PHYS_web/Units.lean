import Mathlib
/-- SI base units -/
inductive BaseUnit
| m | kg | s | A | K | mol | cd
deriving Repr, DecidableEq, BEq, Ord

-- Required for comparisons in sorting
instance : Ord BaseUnit := inferInstance
instance : LT BaseUnit where
  lt x y := compare x y == Ordering.lt

/-- A base unit raised to an integer power -/
structure UnitExp where
  unit : BaseUnit
  power : Int
  deriving Repr, DecidableEq, BEq

/-- A compound unit expression: list of unit exponents -/
abbrev UnitExpr := List UnitExp

/-- A physical quantity with a value and unit -/
structure Quantity where
  value : Float
  units : UnitExpr
  deriving Repr

/-- Pretty print one unit exponent -/
def showUnitExp (u : UnitExp) : String :=
  let base := match u.unit with
    | .m   => "m"
    | .kg  => "kg"
    | .s   => "s"
    | .A   => "A"
    | .K   => "K"
    | .mol => "mol"
    | .cd  => "cd"
  if u.power == 1 then base else base ++ "^" ++ toString u.power

/-- Join a list of strings with a separator -/
def intercalate (sep : String) : List String → String
| []      => ""
| x :: xs => x ++ String.join (xs.map (sep ++ ·))

/-- Pretty print compound unit -/
def showUnit (us : UnitExpr) : String :=
  if us.isEmpty then "1" else intercalate "·" (us.map showUnitExp)

/-- Pretty print quantity -/
def showQuantity (q : Quantity) : String :=
  s!"{q.value} {showUnit q.units}"

instance : ToString Quantity where
  toString := showQuantity

/-- Merge two UnitExpr lists, combining like units -/
def mergeUnits (u1 u2 : UnitExpr) : UnitExpr :=
  let combined := u1 ++ u2
  let grouped := combined.foldl (fun acc u =>
    let (same, rest) := acc.partition (·.unit == u.unit)
    let totalPow := same.foldl (fun p e => p + e.power) u.power
    if totalPow ≠ 0 then ⟨u.unit, totalPow⟩ :: rest else rest
  ) []
  grouped

/-- Multiply two quantities -/
def mulQuantity (q1 q2 : Quantity) : Quantity :=
  {
    value := q1.value * q2.value,
    units := mergeUnits q1.units q2.units
  }

/-- Divide two quantities -/
def divQuantity (q1 q2 : Quantity) : Quantity :=
  let invUnits := q2.units.map (fun ⟨u, p⟩ => ⟨u, -p⟩)
  {
    value := q1.value / q2.value,
    units := mergeUnits q1.units invUnits
  }

/-- Insertion sort on UnitExpr based on unit order -/
def sortUnits : UnitExpr → UnitExpr
| [] => []
| x :: xs =>
  let sorted := sortUnits xs
  let (before, after) := sorted.span (fun y => compare x.unit y.unit == Ordering.gt)
  before ++ [x] ++ after

/-- Check unit equality (up to order) -/
def sameUnits (u1 u2 : UnitExpr) : Bool :=
  sortUnits u1 == sortUnits u2

/-- Quantity equality with unit equivalence -/
def eqQuantity (q1 q2 : Quantity) : Bool :=
  q1.value == q2.value && sameUnits q1.units q2.units

/-- Define some basic quantities -/
def meter    : Quantity := ⟨1.0, [⟨.m, 1⟩]⟩
def second   : Quantity := ⟨1.0, [⟨.s, 1⟩]⟩
def kilogram : Quantity := ⟨1.0, [⟨.kg, 1⟩]⟩

/-- Derived quantity: newton (kg·m/s²) -/
def newton : Quantity :=
  mulQuantity kilogram (divQuantity meter (mulQuantity second second))

/-- Derived quantity: joule (N·m = kg·m²/s²) -/
def joule : Quantity :=
  mulQuantity newton meter
