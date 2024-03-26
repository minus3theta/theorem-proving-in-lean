structure Point (α : Type u) where
  x : α
  y : α
  deriving Repr

#check Point.rec
#check Point.x

def Point.add (p q : Point Nat) :=
  mk (p.x + q.x) (p.y + q.y)

def p : Point Nat := Point.mk 1 2
def q : Point Nat := Point.mk 3 4

#eval p.add q

def Point.smul (n : Nat) (p : Point Nat) :=
  Point.mk (n * p.x) (n * p.y)

#eval p.smul 3

#check { x := 10, y := 20 : Point Nat }

inductive Color where
  | red | green | blue

structure ColorPoint (α : Type u) extends Point α where
  c : Color

#check ColorPoint.mk
#check ColorPoint.toPoint
#check { x := 10, y := 20, c := Color.red : ColorPoint Nat }
#check ColorPoint.mk { x := 10, y := 20 } Color.red

structure Point3 (α : Type u) where
  x : α
  y : α
  z : α

structure RGBValue where
  red : Nat
  green : Nat
  blue : Nat

structure RedGreenPoint (α : Type u) extends Point3 α, RGBValue where
  no_blue : blue = 0

#check RedGreenPoint.mk

def p3 : Point3 Nat := {x := 10, y := 10, z := 20 }
def rgp : RedGreenPoint Nat :=
  { p3 with red := 200, green := 40, blue := 0, no_blue := rfl }

structure Yz (α : Type u) where
  y : α
  z : α

structure Xyyz (α : Type u) extends Point α, Yz α

def xyyz : Xyyz Nat := { x := 10, y := 20, z := 30 }
#check Xyyz.mk
