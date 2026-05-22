import Mathlib

namespace TwoSiteBoolean

namespace bubble

def D0 (D : ℚ) : ℚ := D
def D1 (D e1 : ℚ) : ℚ := D + e1
def D2 (D e2 : ℚ) : ℚ := D + e2
def D3 (D e1 e2 : ℚ) : ℚ := D + e1 + e2

theorem fin_diff_identity_bubble
    (D e1 e2 : ℚ)
    (h0 : D0 D ≠ 0)
    (h1 : D1 D e1 ≠ 0)
    (h2 : D2 D e2 ≠ 0)
    (h12 : D3 D e1 e2 ≠ 0) :
    1 / D0 D
      - 1 / D1 D e1
      - 1 / D2 D e2
      + 1 / D3 D e1 e2
    =
    e1 * e2 *
      (1 / (D0 D * D1 D e1 * D3 D e1 e2)
       + 1 / (D0 D * D2 D e2 * D3 D e1 e2)) := by
  simp [D0, D1, D2, D3] at h0 h1 h2 h12 ⊢
  field_simp [h0, h1, h2, h12]
  ring

end bubble


namespace sunset

def D0 (D : ℚ) : ℚ := D
def D1 (D e1 : ℚ) : ℚ := D + e1
def D2 (D e2 : ℚ) : ℚ := D + e2
def D3 (D e3 : ℚ) : ℚ := D + e3
def D4 (D e1 e2 : ℚ) : ℚ := D + e1 + e2
def D5 (D e1 e3 : ℚ) : ℚ := D + e1 + e3
def D6 (D e2 e3 : ℚ) : ℚ := D + e2 + e3
def D7 (D e1 e2 e3 : ℚ) : ℚ := D + e1 + e2 + e3

theorem fin_diff_identity_sunset
    (D e1 e2 e3 : ℚ)
    (h0 : D0 D ≠ 0)
    (h1 : D1 D e1 ≠ 0)
    (h2 : D2 D e2 ≠ 0)
    (h3 : D3 D e3 ≠ 0)
    (h4 : D4 D e1 e2 ≠ 0)
    (h5 : D5 D e1 e3 ≠ 0)
    (h6 : D6 D e2 e3 ≠ 0)
    (h7 : D7 D e1 e2 e3 ≠ 0) :
    1 / D0 D
      - 1 / D1 D e1
      - 1 / D2 D e2
      - 1 / D3 D e3
      + 1 / D4 D e1 e2
      + 1 / D5 D e1 e3
      + 1 / D6 D e2 e3
      - 1 / D7 D e1 e2 e3
    =
    e1 * e2 * e3 *
      (1 / (D0 D * D1 D e1 * D4 D e1 e2 * D7 D e1 e2 e3)
       + 1 / (D0 D * D1 D e1 * D5 D e1 e3 * D7 D e1 e2 e3)
       + 1 / (D0 D * D2 D e2 * D4 D e1 e2 * D7 D e1 e2 e3)
       + 1 / (D0 D * D2 D e2 * D6 D e2 e3 * D7 D e1 e2 e3)
       + 1 / (D0 D * D3 D e3 * D5 D e1 e3 * D7 D e1 e2 e3)
       + 1 / (D0 D * D3 D e3 * D6 D e2 e3 * D7 D e1 e2 e3)) := by
  simp [D0, D1, D2, D3, D4, D5, D6, D7] at h0 h1 h2 h3 h4 h5 h6 h7 ⊢
  field_simp [h0, h1, h2, h3, h4, h5, h6, h7]
  ring

end sunset

end TwoSiteBoolean
