-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Small34Certificate

namespace Turan

theorem small34_sign_upper (x y : ℝ) (hy : 5/7 ≤ y) :
    0 < (small34ZUpper x y).re - 44*(small34ZUpper x y).im :=
  small34_upper_certificate x y hy

theorem small34_sign_lower (x y : ℝ) (hy : 5/7 ≤ y) :
    0 < (small34ZLower x y).re - 14*(small34ZLower x y).im :=
  small34_lower_certificate x y hy

end Turan
