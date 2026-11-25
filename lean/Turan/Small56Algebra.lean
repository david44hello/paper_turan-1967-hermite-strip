-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Defs
import Mathlib.Tactic

noncomputable section
namespace Turan.Small56
open Polynomial

/-- Eliminating the product of the two shifted nodes gives this equation for their sum. -/
def eliminant (S : ℝ) : ℝ :=
  82*S^10 - 830*S^9 + 2765*S^8 - 1580*S^7 - 9965*S^6 + 21026*S^5 - 14945*S^4 + 11860*S^3 - 18445*S^2 + 7740*S + 2592

def numerator (S : ℝ) : ℝ :=
  -205*S^3 + 635*S^2 - 255*S - 225

def denominator (S : ℝ) : ℝ :=
  32*S^6 - 240*S^5 + 600*S^4 - 540*S^3 + 180*S^2 - 532*S + 540

def nodeProduct (S : ℝ) := numerator S / denominator S

/-- Constant remainder of H₅(w−1/2) modulo w²−Sw+p. -/
def remainder5 (S p : ℝ) := -32*S^3*p + 80*S^2*p + 64*S*p^2 + 80*S*p - 80*p^2 - 200*p - 41

private def slope5 (S p : ℝ) := 32*S^4 - 80*S^3 - 96*S^2*p - 80*S^2 + 160*S*p + 200*S + 32*p^2 + 80*p + 10

theorem remainder5_zero {S : ℝ} (hT : eliminant S = 0) (hD : denominator S ≠ 0) :
    remainder5 S (nodeProduct S) = 0 := by
  unfold remainder5 nodeProduct
  field_simp
  unfold numerator denominator eliminant at *
  linear_combination (2048*S^2 - 5120*S + 3200) * hT

private theorem value5 {S p w : ℝ} (hw : w^2-S*w+p=0) (hr : remainder5 S p=0) :
    (hermite 5).eval ((w:ℂ)-1/2) = (w*slope5 S p : ℝ) := by
  norm_num [hermite, eval_sub, eval_mul, nsmul_eq_mul]
  unfold slope5
  push_cast
  have hw' : (w:ℂ)^2-S*w+p=0 := by exact_mod_cast hw
  have hr' : (remainder5 S p : ℂ)=0 := by exact_mod_cast hr
  unfold remainder5 at hr'
  push_cast at hr'
  linear_combination (32*(S:ℂ)^3 - 80*(S:ℂ)^2 - 64*(S:ℂ)*(p:ℂ) - 80*(S:ℂ) + 80*(p:ℂ) + 32*(w:ℂ)^3 + (w:ℂ)^2*(32*(S:ℂ) - 80) + (w:ℂ)*(32*(S:ℂ)^2 - 80*(S:ℂ) - 32*(p:ℂ) - 80) + 200) * hw' + hr'

/-- Constant remainder of H₆(w−1/2) modulo w²−Sw+p. -/
def remainder6 (S p : ℝ) := -64*S^4*p + 192*S^3*p + 192*S^2*p^2 + 240*S^2*p - 384*S*p^2 - 800*S*p - 64*p^3 - 240*p^2 - 60*p + 31

private def slope6 (S p : ℝ) := 64*S^5 - 192*S^4 - 256*S^3*p - 240*S^3 + 576*S^2*p + 800*S^2 + 192*S*p^2 + 480*S*p + 60*S - 192*p^2 - 800*p - 492

theorem remainder6_zero {S : ℝ} (hT : eliminant S = 0) (hD : denominator S ≠ 0) :
    remainder6 S (nodeProduct S) = 0 := by
  unfold remainder6 nodeProduct
  field_simp
  unfold numerator denominator eliminant at *
  linear_combination (163840*S^9 - 1785856*S^8 + 7577600*S^7 - 15564800*S^6 + 15697920*S^5 - 9047040*S^4 + 10315776*S^3 - 12124160*S^2 + 3635200*S + 1152000) * hT

private theorem value6 {S p w : ℝ} (hw : w^2-S*w+p=0) (hr : remainder6 S p=0) :
    (hermite 6).eval ((w:ℂ)-1/2) = (w*slope6 S p : ℝ) := by
  norm_num [hermite, eval_sub, eval_mul, nsmul_eq_mul]
  unfold slope6
  push_cast
  have hw' : (w:ℂ)^2-S*w+p=0 := by exact_mod_cast hw
  have hr' : (remainder6 S p : ℂ)=0 := by exact_mod_cast hr
  unfold remainder6 at hr'
  push_cast at hr'
  linear_combination (64*(S:ℂ)^4 - 192*(S:ℂ)^3 - 192*(S:ℂ)^2*(p:ℂ) - 240*(S:ℂ)^2 + 384*(S:ℂ)*(p:ℂ) + 800*(S:ℂ) + 64*(p:ℂ)^2 + 240*(p:ℂ) + 64*(w:ℂ)^4 + (w:ℂ)^3*(64*(S:ℂ) - 192) + (w:ℂ)^2*(64*(S:ℂ)^2 - 192*(S:ℂ) - 64*(p:ℂ) - 240) + (w:ℂ)*(64*(S:ℂ)^3 - 192*(S:ℂ)^2 - 128*(S:ℂ)*(p:ℂ) - 240*(S:ℂ) + 192*(p:ℂ) + 800) + 60) * hw' + hr'

theorem node_value {S g d : ℝ} (hT : eliminant S = 0) (hD : denominator S ≠ 0)
    (hg : g^2-S*g+nodeProduct S=0) (hd : d^2-S*d+nodeProduct S=0) (a b : ℂ) :
    (family 5 6 a b).eval ((g:ℂ)-1/2) * d = (family 5 6 a b).eval ((d:ℂ)-1/2) * g := by
  simp only [family, eval_add, eval_mul, eval_C, eval_X, eval_one, eval_ofNat,
    value5 hg (remainder5_zero hT hD), value5 hd (remainder5_zero hT hD),
    value6 hg (remainder6_zero hT hD), value6 hd (remainder6_zero hT hD)]
  push_cast
  ring

end Turan.Small56
