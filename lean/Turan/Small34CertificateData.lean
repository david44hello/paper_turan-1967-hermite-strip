module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Small56Certificate

@[expose] public section

namespace Turan.Small34Certificate

open Small56.Certificate (addWith)

abbrev Gaussian := ℤ × ℤ
abbrev Row := List Gaussian
abbrev Table := List Row

def gadd (p q : Gaussian) : Gaussian := (p.1+q.1,p.2+q.2)
def gmul (a c : ℤ) (p : Gaussian) : Gaussian := (a*p.1-c*p.2, c*p.1+a*p.2)

abbrev rowAdd := addWith gadd
abbrev tableAdd := addWith rowAdd

/-- Multiply a row by a + i*(c+d*t). -/
def shiftRow (a c d : ℤ) (p : Row) : Row :=
  rowAdd (p.map (gmul a c)) ((0,0) :: p.map (gmul 0 d))

/-- One linear endpoint factor, in the coordinates
X=(a+b*x)/(1+v*x), Y=5000000+t, with the chart denominator cleared. -/
def endpoint (a b v e σ : ℤ) (p : Table) : Table :=
  let f := 5000000*σ
  tableAdd (p.map (shiftRow (7*(a-e)) f σ))
    ([] :: p.map (shiftRow (7*(b-v*e)) (v*f) (v*σ)))

structure Boxes where
  l₁ : ℤ
  r₁ : ℤ
  l₂ : ℤ
  r₂ : ℤ
  l₃ : ℤ
  r₃ : ℤ
  slope : ℤ

def upper : Boxes := ⟨-1311446,-96251,-1553002,1794300,-308319,2074718,44⟩
def lower : Boxes := ⟨-1311445,-96252,-1553003,1794301,-308318,2074717,14⟩

def copies (a b v l r σ : ℤ) (p : Table) : ℕ → Table
  | 0 => p
  | n+1 => endpoint a b v r σ (endpoint a b v l (-σ) (copies a b v l r σ p n))

def table (P : Boxes) (a b v : ℤ) : Table :=
  let p := copies a b v P.l₃ P.r₃ 1 [[(1,0)]] 2
  let q := copies a b v P.l₂ P.r₂ (-1) p 4
  copies a b v P.l₁ P.r₁ 1 q 5

/-- Subtract one before checking nonnegativity, so the conclusion is strict. -/
def test (P : Boxes) (a b v : ℤ) : Bool :=
  (tableAdd [[(-1,0)]] (table P a b v)).all (fun row =>
    row.all (fun z => decide (0 ≤ z.1-P.slope*z.2)))

end Turan.Small34Certificate
