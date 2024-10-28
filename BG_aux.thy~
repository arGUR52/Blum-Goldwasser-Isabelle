theory BG_aux 
imports Sigma_Commit_Crypto.Number_Theory_Aux 
begin 

section "Auxillary Lemmas"

text "Here, we have all the auxillary definitions used in the formalization of Blum-Goldwasser cryptosystem"


section "Auxillary Lemmas"

text "Here, we have all the auxillary lemmas used to prove the correctness of Blum-Goldwasser cryptosystem"

(*Euler's criterion does not exist in Isabelle, should be proven.
  This is just a preliminary attempt at proving it - going to look into it 
  further after the formalization is done *)
lemma eulers_criterion:
  assumes "prime (p :: nat)" "p = 2 * p_2 + 1" "\<not> p dvd x"
  shows "if (\<exists>y. y^2 = x) then [x^(p_2) = 1] (mod p) else [x^(p_2) = -1] (mod p)"
proof -
  from assms fermat_theorem
  have "[x ^ (p - 1) = 1] (mod p)"
    by algebra
  then have "[x ^ (p - 1) - 1 = 0] (mod p)"
    using cong_0_iff cong_to_1_nat 
    by blast
  then have "[(x ^ p_2 - 1) * (x ^ p_2 + 1) = 0] (mod p)"
    using Nat.add_diff_assoc2 add.commute add_diff_cancel_left' assms(2) 
   distrib_left linorder_not_less mult.right_neutral mult_eq_if not_add_less1 
   power2_eq_square power_even_eq
    by (smt (verit))
  then show ?thesis 
    sorry
qed




end