import number_theory.sum_two_squares
import number_theory.modular
import data.zmod.basic
/-
(pg 21) Lemma 2: No number n=4m+3 is a sum of 2 squares

The sum of any even number is (2k)^2= 4k^2 = 0 (mod 4)
while the squares of odd numbers yield (2k+1)^2=1 (mod 4)
Thus, any sum of squares is 0,1 or 2 (mod 4)
-/
lemma no_sum_of_sq_4m_3:  ∀ a b m,  a*a+b*b ≠ 4*m+3 := begin
  intro a,
  intro b,
  intro m,
  by_contradiction,
  by_cases ha : even a, -- split on whether even or odd
  by_cases hb : even b, -- split on whether even or odd
  {
    have x : (a: zmod 4)*a = 0 := begin
      norm_fin,
      sorry,
    end,
      have y : (b: zmod 4)*b = 0 := begin
      norm_fin,
      sorry,
    end,
    have z : (a: zmod 4)*a + (b: zmod 4)*b  = 0 := begin
      norm_fin,
      sorry,
    end,
    have fh: a * a + b * b =  3 := begin
      sorry,
    end,
    contradiction,
    sorry,
  },
  {

    sorry,
  },
  {

    sorry,
  },
  -- {

  --   -- sorry,
  -- },
end