import data.nat.prime
import tactic.linarith
import algebra.big_operators.order
import data.nat.interval
import data.nat.prime
import data.nat.modeq
import tactic

open_locale big_operators
open nat

/-
(pg 3) Euclid's Proof that there are infiinitely many primes
-/

theorem infinitude_of_primes : ∀ N, ∃ p ≥ N, nat.prime p :=
begin
  intro N,
  let M := nat.factorial N + 1,
  let p := min_fac M ,
  have pp:  nat.prime p := begin
    refine min_fac_prime _,
    have x :   nat.factorial N > 0 := begin
      exact factorial_pos N,
    end,
    linarith,
  end,
  use p,
  split,
  { by_contradiction, 
    have np : p ≤ N, from le_of_not_ge h,
    have h1 : p ∣ nat.factorial N,from dvd_factorial (min_fac_pos _) np,
    have h2 : p ∣ 1, from (nat.dvd_add_iff_right h1).2 (min_fac_dvd _),
    exact nat.prime.not_dvd_one pp h2,
    },
  { exact pp }
end




-- define a fermat number
def fermat_number (p : ℕ ) := 2^2^p +1
-- p is a fermat number
def is_fermat_number (p: ℕ ): Prop := ∃ N, fermat_number N = p

lemma fermat_recurrence (n: ℕ) : ∏ x in finset.range n, fermat_number x = fermat_number n - 2 :=
begin
  simp only [fermat_number],
  induction n with n ih,
  { simp },
  { simp only [nat.succ_eq_add_one, finset.prod_range_succ, nat.succ_sub_succ_eq_sub,
      finset.prod_congr, ih],
    rw [mul_comm, ←nat.sq_sub_sq, pow_succ' _ n, pow_mul, one_pow], }
end
lemma fermat_numbers_relatively_prime' :   ∀ a b, is_fermat_number a ∧ is_fermat_number b → nat.coprime a b := begin
  intros a b fa,
  have : a > b := begin 
    -- tactic.wlog a b,
    sorry,
  end, 
  cases fa,
  have fermat_recurrence := fermat_recurrence,
  by_contradiction,
  let m := gcd a b,
  have x:  m > 1  := sorry, 
  have fermat_a:  ∏ (x : ℕ) in finset.range a, fermat_number x = fermat_number a - 2 := begin
    rw fermat_recurrence,
  end,
  have fermat_mod :  (∏ (x : ℕ) in finset.range a, fermat_number x)  ≡ (fermat_number a - 2) [MOD m] := begin
    simp [modeq_iff_dvd],
    sorry,
  end,
  have fermat_mod_l :  (∏ (x : ℕ) in finset.range a, fermat_number x)  ≡ 0 [MOD m] := begin
    rw modeq_iff_dvd,
    norm_num,
    sorry,
  end,
  sorry,
end
-- prove all fermat numbers are coprime
lemma fermat_numbers_relatively_prime :   ∀ a b, is_fermat_number a ∧ is_fermat_number b → nat.coprime a b := begin
  intro a,
  intro b,
  intro fa,
  cases fa,
  let m  := nat.gcd a b,
  have h2 : m ∣ 2 := begin
    refine dvd_of_mem_factors _,
    sorry,
  end,
  have w : m = 1 := begin
  refine nat.dvd_one.mp _,
  refine nat.dvd_one.mpr _,
    sorry,
  end,
  refine coprime_iff_gcd_eq_one.mpr w,
end

/-
(pg 3) Fermat number proof that there are infinitely 
many primes
-/
theorem fermat_numbers_infinitely_many_primes : ∀ N, ∃ p ≥ N, nat.prime p :=
begin
 sorry,
end