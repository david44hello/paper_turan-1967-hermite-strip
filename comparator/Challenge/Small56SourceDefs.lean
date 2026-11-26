module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Challenge.Small56NodeDef

@[expose] public section
noncomputable section
namespace Turan.Small56
/-- Denominator in the elimination formula for the two shifted nodes. -/
def denominator (S : ℝ) : ℝ :=
  32*S^6 - 240*S^5 + 600*S^4 - 540*S^3 + 180*S^2 - 532*S + 540

def remainder5 (S p : ℝ) := -32*S^3*p + 80*S^2*p + 64*S*p^2 + 80*S*p - 80*p^2 - 200*p - 41
def remainder6 (S p : ℝ) := -64*S^4*p + 192*S^3*p + 192*S^2*p^2 + 240*S^2*p - 384*S*p^2 - 800*S*p - 64*p^3 - 240*p^2 - 60*p + 31
def lower (e : Entry) := (|(e.G:ℝ)|-2)/(|(e.D:ℝ)|+2)
namespace Certificate
def gamma : List ℤ := [-2048845,-2048845,2907699,2907699,2222962,2222962,2222962,
  -555650,-555650,-555650,-555650,360845]

def delta : List ℤ := [-75660,-75660,-1805569,-1805569,-626158,-626158,-626158,
  2384521,2384521,2384521,2384521,2327565]
end Certificate
end Turan.Small56
