-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.QuarticPencilCertificate

noncomputable section
namespace Turan.QuarticPencil

/-- Resultant of `12 X³ + a X² + b X + c` and `j X² + k X + l`. -/
private def resultant (a b c j k l : ℝ) : ℝ :=
  a^2*j*l^2 - a*b*j*k*l - 2*a*c*j^2*l + a*c*j*k^2 - 12*a*k*l^2
    + b^2*j^2*l - b*c*j^2*k - 24*b*j*l^2 + 12*b*k^2*l
    + c^2*j^3 + 36*c*j*k*l - 12*c*k^3 + 144*l^3

private theorem resultant_zero {a b c j k l x : ℝ}
    (hc : 12*x^3 + a*x^2 + b*x + c = 0) (hq : j*x^2 + k*x + l = 0) :
    resultant a b c j k l = 0 := by
  rw [show c = -(12*x^3 + a*x^2 + b*x) by linarith only [hc],
    show l = -(j*x^2 + k*x) by linarith only [hq]]
  unfold resultant
  ring

/-- Eliminate the real part of a nonreal pencil root. Divide the imaginary
equation by `4 * im(z)` to get the cubic. Subtract a linear multiple
of that cubic from the real equation to get the quadratic. -/
theorem height_equation (d : ℝ) (z : ℂ) (hy : z.im ≠ 0)
    (hz : (2*z+(d:ℂ))^2*(4*z^2+4*z+2) - (4*z^4-4*z^2+3) = 0) :
    let t := 3*z.im^2 - 2
    base t + d^2 * (evenPart t (d^2) + (d-4)^2 * squarePart t (d^2)) = 0 := by
  let x := z.re
  let v := z.im^2
  let a := 12*(d+1)
  let b := 2*d^2+8*d-12*v+6
  let c := d^2-4*d*v+2*d-4*v
  let j := -6*d^2-180*v+6
  let k := -2*d^3-d^2-120*d*v+4*d-120*v-6
  let l := -d^3-8*d^2*v+3*d^2-40*d*v-2*d+36*v^2-32*v-9
  have hi := congrArg Complex.im hz
  have hr := congrArg Complex.re hz
  norm_num [pow_succ, Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re,
    Complex.sub_im, Complex.sub_re] at hi hr
  have hc : 12*x^3 + a*x^2 + b*x + c = 0 := by
    apply (mul_eq_zero.mp (show z.im * (12*x^3 + a*x^2 + b*x + c) = 0 by
      dsimp [a,b,c,x,v]
      linear_combination hi / 4)).resolve_left hy
  have hq : j*x^2 + k*x + l = 0 := by
    dsimp [a,b,c,x,v] at hc
    dsimp [j,k,l,x,v]
    linear_combination 3*hr - (3*z.re+d+1)*hc
  have h := resultant_zero hc hq
  have ident (d v : ℝ) :
      4*(base (3*v-2) + d^2 * (evenPart (3*v-2) (d^2) +
        (d-4)^2 * squarePart (3*v-2) (d^2))) =
      3*resultant (12*(d+1)) (2*d^2+8*d-12*v+6) (d^2-4*d*v+2*d-4*v)
        (-6*d^2-180*v+6) (-2*d^3-d^2-120*d*v+4*d-120*v-6)
        (-d^3-8*d^2*v+3*d^2-40*d*v-2*d+36*v^2-32*v-9) := by
    unfold base evenPart squarePart resultant
    ring
  change base (3*v-2) + d^2 * (evenPart (3*v-2) (d^2) +
    (d-4)^2 * squarePart (3*v-2) (d^2)) = 0
  have hid := ident d v
  rw [h, mul_zero] at hid
  exact (mul_eq_zero.mp hid).resolve_left (by norm_num)

end Turan.QuarticPencil
