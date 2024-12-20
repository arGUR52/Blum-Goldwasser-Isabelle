theory BG_correctness imports
  Main
  BG_formalization

begin

text "Correctness proof"

lemma l_set_less_h: "l \<in> set (split m h) \<Longrightarrow> length l \<le> h"   
    proof (induction m h rule: split.induct)
      case (1 n)
      then show ?case by auto
    next
      case (2 v va)
      then consider (m_empty) "m = []" | (m_not_empty) "m \<noteq> []" by auto
      then show ?case
    proof cases
      case m_empty
      then show ?thesis using 2 by auto
    next
      case m_not_empty
      then have "\<exists>x xs. m = x # xs" by (auto iff: neq_Nil_conv)
      then show ?thesis using 2 by (auto)
    qed
    next
      case (3 x xs v)
      have "split (x # xs) (Suc v) = (take (Suc v) (x # xs)) # (split (drop (Suc v) (x # xs)) (Suc v))"
            using split.elims 
            by auto
      then have "l \<in> set ((take (Suc v) (x # xs)) # (split (drop (Suc v) (x # xs)) (Suc v)))"
        using 3(2) by auto

      then have "l = take (Suc v) (x # xs) \<or> l \<in> set (split (drop (Suc v) (x # xs)) (Suc v))" by auto
      then consider "l = (take (Suc v) (x # xs))" | "l \<in> set (split (drop (Suc v) (x # xs)) (Suc v))" by blast
      then show "length l \<le> Suc v"
      proof cases
        case 1
        then show ?thesis by auto
      next
        case 2
        then show ?thesis using 3(1) by auto
      qed
    qed
   

corollary split_l: "\<forall>l \<in> set (split m h). length l \<le> h" 
  using l_set_less_h by auto

lemma x_exp: 
  assumes "p mod 4 = 3" "q mod 4 = 3" (*pq_cong_3*)
    "prime (p::nat)" "prime q" (*pq_prime*)
    "coprime x (p * q)" "\<exists>r. [x = r * r] (mod p * q)"
  shows "[(x ^ (2 ^ (t + 1))) ^ (((p + 1) div 4) ^ (t + 1)) = x] (mod p)"
proof (induction t)
  case 0
  have "(x ^ (2 ^ (0 + 1))) ^ (((p + 1) div 4) ^ (0 + 1)) 
      = (x ^ (2 ^ 1)) ^ (((p + 1) div 4) ^ 1)" by auto
  then have  "(x ^ (2 ^ (0 + 1))) ^ (((p + 1) div 4) ^ (0 + 1)) 
      = (x ^ 2) ^ ((p + 1) div 4)" by auto
  
  then have x_mod_1: "(x ^ (2 ^ (0 + 1))) ^ (((p + 1) div 4) ^ (0 + 1)) 
      = x ^ (2 * ((p + 1) div 4))" 
    using power_mult[symmetric] by auto
  from assms(1) have "[p = 3] (mod 4)" 
    by (simp add: unique_euclidean_semiring_class.cong_def)
  then have "[p + 1 = 3 + 1] (mod 4)" 
  using cong_add_rcancel_nat by blast
  then have "[p + 1 = 0] (mod 4)" 
    by (simp add: unique_euclidean_semiring_class.cong_def)
  then have "4 dvd p + 1" 
    using cong_0_iff by blast
  then have "x ^ (2 * ((p + 1) div 4)) = x ^ ((p + 1) div 2)" 
    by auto
  from x_mod_1 this have x_mod_2: "(x ^ (2 ^ (0 + 1))) ^ (((p + 1) div 4) ^ (0 + 1)) =  x ^ ((p + 1) div 2)" 
    by auto

  from x_mod_2 assms(1) assms(3) have p_greater_3: "p \<ge> 3" by auto
  from assms(3) have odd_p: "odd p" 
    by (simp add: assms(1) even_even_mod_4_iff)
  from odd_p p_greater_3 have p_add_1[symmetric]: "(p + 1) div 2 = 1 + (p - 1) div 2" 
   by linarith
  from this x_mod_2 odd_p p_greater_3 have "(x ^ (2 ^ (0 + 1))) ^ (((p + 1) div 4) ^ (0 + 1)) =  x ^ (1 + (p - 1) div 2)" 
    by auto
  then have "(x ^ (2 ^ (0 + 1))) ^ (((p + 1) div 4) ^ (0 + 1)) =  x * x ^ ((p - 1) div 2)" by auto
  then have x_x_p: "[(x ^ (2 ^ (0 + 1))) ^ (((p + 1) div 4) ^ (0 + 1)) = x * x ^ ((p - 1) div 2)] (mod p)" 
    by auto
  from assms(5) have coprime_xp: "coprime x p" by auto
  then have coprime_px: "coprime p x" 
    using coprime_commute by auto
  from assms(6) have "\<exists>r. [x = r * r] (mod p)"
    using cong_modulus_mult_nat by blast
  then have x_is_squared: "\<exists>r. [r^2 = x] (mod p)" 
    by (simp add: cong_sym_eq power2_eq_square)

  from eulers_criterion assms(3) odd_p coprime_px x_is_squared have euler_thm: "[x ^ ((p - 1) div 2) = 1] (mod p)" 
    by auto
  have "[x = x] (mod p)" by auto
  from this euler_thm have "[x * x ^ ((p - 1) div 2) = x * 1] (mod p)" using cong_mult by blast
  then have "[x * x ^ ((p - 1) div 2) = x] (mod p)" by auto
  from this x_x_p show "?case" using cong_trans by auto
next
  case (Suc t)
  assume "[(x ^ 2 ^ (t + 1)) ^ ((p + 1) div 4) ^ (t + 1) = x] (mod p)"

  then have "[((x ^ 2 ^ (t + 1)) ^ ((p + 1) div 4) ^ (t + 1)) ^ ((p + 1) div 4) = x ^ ((p + 1) div 4)] (mod p)" 
    using cong_pow by blast

  from assms(1) have "[p = 3] (mod 4)" 
    by (simp add: unique_euclidean_semiring_class.cong_def)
  then have "[p + 1 = 3 + 1] (mod 4)" 
  using cong_add_rcancel_nat by blast
  then have "[p + 1 = 0] (mod 4)" 
    by (simp add: unique_euclidean_semiring_class.cong_def)
  then have p_dvd_by_4: "4 dvd p + 1" 
    using cong_0_iff by blast
  
  from assms(1) assms(3) have p_greater_3: "p \<ge> 3" by auto
  from assms(3) have odd_p: "odd p"
    by (simp add: assms(1) even_even_mod_4_iff)
  from odd_p p_greater_3 have p_add_1[symmetric]: "(p + 1) div 2 = 1 + (p - 1) div 2" 
   by linarith
  have x_refl: "[x = x] (mod p)" by auto

  from assms(5) have coprime_xp: "coprime x p" by auto
  then have coprime_p_x: "coprime p x" using coprime_commute by blast
  from assms(6) have "\<exists>r. [x = r * r] (mod p)"
    using cong_modulus_mult_nat by blast
  then have x_is_squared: "\<exists>r. [r^2 = x] (mod p)" 
    by (auto simp add: cong_sym_eq power2_eq_square)
  
  from eulers_criterion assms(3) odd_p coprime_p_x x_is_squared have euler_thm: "[x ^ ((p - 1) div 2) = 1] (mod p)"
    by auto

  from this x_refl have "[x * x ^ ((p - 1) div 2) = x * 1] (mod p)" using cong_mult by blast
  then have cong_xx: "[x * x ^ ((p - 1) div 2) = x] (mod p)" by auto
  have "x * x ^ ((p - 1) div 2) = x ^ (1 + (p - 1) div 2)" using powr_add by auto
  then have "x * x ^ ((p - 1) div 2) = x ^ ((p + 1) div 2)" using p_add_1 by algebra
  from cong_xx this have "[x ^ ((p + 1) div 2) = x] (mod p)" by auto

  from this Suc have cong_1: "[((x ^ 2 ^ (t + 1)) ^ ((p + 1) div 4) ^ (t + 1)) ^ ((p + 1) div 2) = x] (mod p)" 
    using cong_pow cong_trans by blast


 
  have help_1: "(((p + 1) div 4) ^ (t + 2)) * 2 = 2 * (((p + 1) div 4) ^ (t + 2))" by auto
  have help_2: "(((p + 1) div 4) ^ (t + 1)) * ((p + 1) div 4) * 2 = (((p + 1) div 4) ^ (t + 2)) * 2 " by auto

  from p_dvd_by_4 have div_div[symmetric]: "((p + 1) div 4) * 2 = (p + 1) div 2" by fastforce 
  
  have eq_1: "((x ^ 2 ^ (t + 1)) ^ ((p + 1) div 4) ^ (t + 1)) ^ ((p + 1) div 2)
      = ((x ^ 2 ^ (t + 1)) ^ ((((p + 1) div 4) ^ (t + 1)) * ((p + 1) div 2)))" 
    by (simp add: power_mult)
  also have eq_2: " ((x ^ 2 ^ (t + 1)) ^ ((((p + 1) div 4) ^ (t + 1)) * ((p + 1) div 2)))
      = ((x ^ 2 ^ (t + 1)) ^ ((((p + 1) div 4) ^ (t + 1)) * ((p + 1) div 4) * 2))"  
    using div_div by (auto simp add:  more_arith_simps(11))
  then also have eq_3: " ((x ^ 2 ^ (t + 1)) ^ ((((p + 1) div 4) ^ (t + 1)) * ((p + 1) div 4) * 2))
      = ((x ^ 2 ^ (t + 1)) ^ ((((p + 1) div 4) ^ (t + 2)) * 2))"  
    using help_2 by algebra

  also have eq_4:  " ((x ^ 2 ^ (t + 1)) ^ ((((p + 1) div 4) ^ (t + 2)) * 2))
      = ((x ^ 2 ^ (t + 1)) ^  (2 * (((p + 1) div 4) ^ (t + 2))))" using help_1 by algebra
  
  also have eq_5: "((x ^ 2 ^ (t + 1)) ^  (2 * (((p + 1) div 4) ^ (t + 2))))
      = (((x ^ 2 ^ (t + 1)) ^ 2) ^  (((p + 1) div 4) ^ (t + 2)))"
    using power_mult by auto
  also have eq_6: "(((x ^ 2 ^ (t + 1)) ^ 2) ^  (((p + 1) div 4) ^ (t + 2)))
      = ((x ^ (2 ^ (t + 1) * 2)) ^  (((p + 1) div 4) ^ (t + 2)))" 
    using power_mult[symmetric] by metis
  also have eq_7: " ((x ^ (2 ^ (t + 1) * 2)) ^  (((p + 1) div 4) ^ (t + 2))) =
      (x ^ (2 ^ (t + 2))) ^ (((p + 1) div 4) ^ (t + 2))" by auto
  also have eq_8: "(x ^ (2 ^ (t + 2))) ^ (((p + 1) div 4) ^ (t + 2)) 
  = (x ^ (2 ^ (Suc t + 1))) ^ (((p + 1) div 4) ^ (Suc t + 1))" by auto
  from cong_1 x_refl show "?case" 
    using calculation by auto
qed



lemma exp_mod_prime_p: 
  assumes "prime p" "coprime a p"
  shows "[a ^ b = a ^ (b mod (p - 1))] (mod p)" 
proof -
  from euler_theorem assms(2) have "[a ^ (totient p) = 1] (mod p)" by auto
  from this totient_prime assms(1) have a_mod_1: "[a ^ (p - 1) = 1] (mod p)" by auto
  from mod_div_decomp have b_decomp: "b = (b div (p - 1)) * (p - 1) + (b mod (p - 1))" by auto
  then have a_exp_decomp: "[a ^ b = a ^ ((b div (p - 1)) * (p - 1) + (b mod (p - 1)))] (mod p)" by auto

  have a_Dec1: "a ^ ((b div (p - 1)) * (p - 1) + (b mod (p - 1))) = a ^ ((b div (p - 1)) * (p - 1)) * a ^ (b mod (p - 1))" 
    using power_add by blast
  also have a_Dec2: "a ^ ((b div (p - 1)) * (p - 1)) * a ^ (b mod (p - 1)) = a ^ ((p - 1) * (b div (p - 1))) * a ^ (b mod (p - 1))" 
    by (simp add: Groups.mult_ac(2))
  also have "a ^ ((p - 1) * (b div (p - 1))) =  (a ^ (p - 1)) ^ (b div (p - 1))" 
    using power_mult by blast
  from this a_Dec1 a_Dec2 have "a ^ ((b div (p - 1)) * (p - 1) + (b mod (p - 1)))  =  (a ^ (p - 1)) ^ (b div (p - 1)) * a ^ (b mod (p - 1))" 
    by auto

  from a_exp_decomp this have a_b_cong: "[a ^ b = (a ^ (p - 1)) ^ (b div (p - 1)) * a ^ (b mod (p - 1))] (mod p)" by auto
  from a_mod_1 have a_exp_mod_1: "[(a ^ (p - 1)) ^ (b div (p - 1)) = 1] (mod p)" using cong_pow by fastforce
  have "[a ^ (b mod (p - 1)) = a ^ (b mod (p - 1))] (mod p)" by auto

  from this a_exp_mod_1 have "[(a ^ (p - 1)) ^ (b div (p - 1)) * a ^ (b mod (p - 1)) = 1 ^ (b div (p - 1)) * a ^ (b mod (p - 1))] (mod p)"
    using  cong_scalar_right by fastforce

  from this a_b_cong have "[a ^ b = 1 ^ (b div (p - 1)) * a ^ (b mod (p - 1))] (mod p)" using cong_trans by fast 
  then show "?thesis" by auto
qed


lemma x_exp_sym: 
  assumes "p mod 4 = 3" "q mod 4 = 3" (*pq_cong_3*)
    "prime (p::nat)" "prime q" (*pq_prime*)
    "coprime x (p * q)" "\<exists>r. [x = r * r] (mod p * q)"
  shows "[(x ^ (2 ^ (t + 1))) ^ (((q + 1) div 4) ^ (t + 1)) = x] (mod q)"
  by (metis Groups.mult_ac(2) assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) x_exp)




lemma same_x_0:
  assumes 
    "p mod 4 = 3" "q mod 4 = 3" (*pq_cong_3*)
    "prime (p::nat)" "prime q" (*pq_prime*)
    "r < p * q" "coprime r (p * q)" 
    "p \<noteq> q"
  shows "
    (let x = r ^ (2 ^ (t + 2)) mod (p * q) in
    let u_p = x ^ (calculate_exponent t p) mod p in
    let u_q = x ^ (calculate_exponent t q) mod q in
    let ((r_p, r_q), _) = euclid_ext p q in
    nat ((int u_q * r_p * int p + int u_p * r_q * int q) mod int (p * q))) = (r ^ 2) mod (p * q)"
proof - 
  let ?xt = "r ^ (2 ^ (t + 2)) mod (p * q)"
  let ?x0 = "(r * r) mod p * q"
  let ?up = "?xt ^ (calculate_exponent t p) mod p"
  let ?uq = "?xt ^ (calculate_exponent t q) mod q"



  have "?xt = r ^ (2 * 2 ^ (t + 1)) mod (p * q)" by auto
  also have "r ^ (2 * 2 ^ (t + 1)) mod (p * q) = (r ^ 2) ^ (2 ^ (t + 1)) mod (p * q)" 
    by (simp add: power_mult)
  then have x_t_def: "?xt = (r ^ 2) ^ (2 ^ (t + 1)) mod (p * q)" by auto

  (*----------------------[u_p = x] (mod p)--------------------------------------------------------*)
  have "[?up = ?xt ^ (calculate_exponent t p)] (mod p)" by auto
  then have u_p_1: "[?up = ?xt ^ (((Suc p) div 4) ^ (Suc t) mod (p-1))] (mod p)" by auto

  from x_t_def assms have "[?xt = (r ^ 2) ^ (2 ^ (t + 1))] (mod p)" 
    using cong_refl mod_mult_cong_right
    by metis

  from u_p_1 this have cong_up: "[?up = ((r ^ 2) ^ (2 ^ (t + 1))) ^ (((Suc p) div 4) ^ (Suc t) mod (p-1))] (mod p)"
    using cong_pow by fastforce

  from assms(6) have "coprime r p" by auto
  then have coprime_xp: "coprime ((r ^ 2) ^ (2 ^ (t + 1))) p" by auto 
  from assms(6) have coprime_r_sq: "coprime (r ^ 2) (p * q)" by auto 

  from coprime_xp assms(3) 
  have "[((r ^ 2) ^ (2 ^ (t + 1))) ^ (((Suc p) div 4) ^ (Suc t)) 
        = ((r ^ 2) ^ (2 ^ (t + 1))) ^ (((Suc p) div 4) ^ (Suc t) mod (p-1))] (mod p)"
    using exp_mod_prime_p by auto
  then have mod_exp_elim: "[((r ^ 2) ^ (2 ^ (t + 1))) ^ (((Suc p) div 4) ^ (Suc t) mod (p-1)) 
            = ((r ^ 2) ^ (2 ^ (t + 1))) ^ (((Suc p) div 4) ^ (Suc t))] (mod p)" 
    using cong_sym by auto

  have "[?up = ?up] (mod p)" by auto
  from cong_up mod_exp_elim have up_eq: "[?up = ((r ^ 2) ^ (2 ^ (t + 1))) ^ (((Suc p) div 4) ^ (Suc t))] (mod p)" 
    using cong_trans by fast

  from assms(1) assms(2) assms(3) assms(4) coprime_r_sq have x_t_to_x_zero: "[((r ^ 2) ^ (2 ^ (t + 1))) ^ (((Suc p) div 4) ^ (Suc t)) = r ^ 2] (mod p)"
    using x_exp cong_refl power2_eq_square semiring_norm(174)
  by (metis)

  from up_eq x_t_to_x_zero have up_cong_x_mod_p:"[?up = r ^ 2] (mod p)" 
    using cong_trans by fast
(*----------------------end: [u_p = x] (mod p)-----------------------------------------------------*)
(*----------------------[u_q = x] (mod q)--------------------------------------------------------*)
  have "[?uq = ?xt ^ (calculate_exponent t q)] (mod q)" by auto
  then have u_q_1: "[?uq = ?xt ^ (((Suc q) div 4) ^ (Suc t) mod (q-1))] (mod q)" by auto

  from x_t_def have "?xt = (r ^ 2) ^ (2 ^ (t + 1)) mod (q * p)" 
    by (simp add: mult.commute)
  from this assms have "[?xt = (r ^ 2) ^ (2 ^ (t + 1))] (mod q)" 
    using cong_refl mod_mult_cong_right
    by metis

  from u_q_1 this have cong_up: "[?uq = ((r ^ 2) ^ (2 ^ (t + 1))) ^ (((Suc q) div 4) ^ (Suc t) mod (q-1))] (mod q)"
    using cong_pow by fastforce

  from assms(6) have "coprime r q" by auto
  then have coprime_xq: "coprime ((r ^ 2) ^ (2 ^ (t + 1))) q" by auto 
  from assms(6) have coprime_r_sq_rev: "coprime (r ^ 2) (q * p)" by auto 

  from coprime_xq assms(4) 
  have "[((r ^ 2) ^ (2 ^ (t + 1))) ^ (((Suc q) div 4) ^ (Suc t)) 
        = ((r ^ 2) ^ (2 ^ (t + 1))) ^ (((Suc q) div 4) ^ (Suc t) mod (q-1))] (mod q)"
    using exp_mod_prime_p by auto

  then have mod_exp_elim: "[((r ^ 2) ^ (2 ^ (t + 1))) ^ (((Suc q) div 4) ^ (Suc t) mod (q-1)) 
            = ((r ^ 2) ^ (2 ^ (t + 1))) ^ (((Suc q) div 4) ^ (Suc t))] (mod q)" 
    using cong_sym by auto

  have "[?up = ?up] (mod q)" by auto
  from cong_up mod_exp_elim have uq_eq: "[?uq = ((r ^ 2) ^ (2 ^ (t + 1))) ^ (((Suc q) div 4) ^ (Suc t))] (mod q)" 
    using cong_trans by fast

  from assms(1) assms(2) assms(3) assms(4) coprime_r_sq
  have x_t_to_x_zero: "[((r ^ 2) ^ (2 ^ (t + 1))) ^ (((Suc q) div 4) ^ (Suc t)) = r ^ 2] (mod q)"
    using x_exp_sym cong_refl power2_eq_square semiring_norm(174)
  by (metis)

  from uq_eq x_t_to_x_zero have up_cong_x_mod_q: "[?uq = r ^ 2] (mod q)" 
    using cong_trans by fast
(*----------------------end: [u_q = x] (mod q)-----------------------------------------------------*)


  have "\<exists>r_p r_q c. (((r_p, r_q), c) = euclid_ext p q)" 
    using surj_pair
    by (metis)
  then obtain r_p r_q c where r_obtain: "(((r_p, r_q), c) = euclid_ext p q)" by blast
  hence c_def: "c = gcd p q" by auto
  from assms(3) assms(4) assms(7) have coprime_pq: "coprime p q" 
    using Primes.primes_coprime_int by auto
  from this c_def have "c = 1" by auto

  from coprime_pq have gcd_pq: "gcd p q = 1" by auto

  from r_obtain have "bezout_coefficients p q = (r_p, r_q)" by auto
  from gcd_pq this have "r_p * p + r_q * q = 1"
    using bezout_coefficients
    by fastforce
  hence "(r ^ 2) * (r_p * p + r_q * q) = (r ^ 2) * 1" by auto
  hence final_eq: "((r ^ 2) * r_p * p + (r ^ 2) * r_q * q) = (r ^ 2)" 
    by (simp add: int_distrib(2))

(*----------------------[x * r_p * p  + x * r_q * q = x] (mod p)------------------------------------*)

  have p_times_mod_0: "[(r ^ 2) * r_p * p = 0] (mod p)"
    using cong_mult_self_right by blast
  from final_eq  
  have "[((r ^ 2) * r_p * p + (r ^ 2) * r_q * q) = (r ^ 2)] (mod p)" by auto
  then have cong_1: "[(r ^ 2) = ((r ^ 2) * r_p * p + (r ^ 2) * r_q * q)] (mod p)" 
    using cong_sym by auto

  have "[(r ^ 2) * r_q * q = (r ^ 2) * r_q * q] (mod p)" by auto
  
  from this p_times_mod_0
  have cong_2: "[((r ^ 2) * r_p * p + (r ^ 2) * r_q * q) = 0 + (r ^ 2) * r_q * q] (mod p)" 
    using cong_add by fastforce
  from cong_1 cong_2 
  have "[(r ^ 2) = 0 + (r ^ 2) * r_q * q] (mod p)" 
    using  cong_trans
   by fastforce
  hence p_cong: "[(r ^ 2) = (r ^ 2) * r_q * q] (mod p)" by auto
  from up_cong_x_mod_p have up_cong: "[(r ^ 2) = ?up] (mod p)" using cong_sym by auto
  from p_cong up_cong 
  have p_cong_u: "[(r ^ 2) = ?up * r_q * q] (mod p)"
    using cong_int_iff cong_scalar_right cong_trans
  by (smt (verit, ccfv_threshold) )

  have p_times_mod_0: "[?uq * r_p * p = 0] (mod p)"
    using cong_mult_self_right by blast 
  from p_cong_u have "[?up * r_q * q = (r ^ 2)] (mod p)" using cong_sym_eq by blast
  from this p_times_mod_0 have p_cong_u2: "[(?uq * r_p * p + ?up * r_q * q) = (r ^ 2)] (mod p)" 
    using cong_add by fastforce

(*----------------------end: [x * r_p * p  + x * r_q * q = x] (mod p)--------------------------------*)
(*----------------------[x * r_p * p  + x * r_q * q = x] (mod q)-------------------------------------*)
  
  have q_times_mod_0: "[(r ^ 2) * r_q * q = 0] (mod q)"
    using cong_mult_self_right by blast
  from final_eq  
  have "[((r ^ 2) * r_p * p + (r ^ 2) * r_q * q) = (r ^ 2)] (mod q)" by auto
  then have cong_1: "[(r ^ 2) = ((r ^ 2) * r_p * p + (r ^ 2) * r_q * q)] (mod q)" 
    using cong_sym by auto

  have "[(r ^ 2) * r_p * p = (r ^ 2) * r_p * p] (mod q)" by auto
  
  from this q_times_mod_0
  have cong_2: "[((r ^ 2) * r_p * p + (r ^ 2) * r_q * q) = (r ^ 2) * r_p * p + 0] (mod q)" 
    using cong_add by fast
  from cong_1 cong_2 
  have "[(r ^ 2) = 0 + (r ^ 2) * r_p * p] (mod q)" 
    using cong_trans
   by fastforce
  hence q_cong: "[(r ^ 2) = (r ^ 2) * r_p * p] (mod q)" by auto
  
  from up_cong_x_mod_q have uq_cong: "[(r ^ 2) = ?uq] (mod q)" using cong_sym by auto
  from q_cong uq_cong 
  have q_cong_u: "[(r ^ 2) = ?uq * r_p * p] (mod q)"
    using cong_int_iff cong_scalar_right cong_trans
    by (smt (verit, ccfv_threshold) )


  have q_times_mod_0: "[?up * r_q * q = 0] (mod q)"
    using cong_mult_self_right by blast 
  from q_cong_u have "[?uq * r_p * p = (r ^ 2)] (mod q)" using cong_sym_eq by blast
  from this q_times_mod_0 have q_cong_u2: "[(?uq * r_p * p + ?up * r_q * q) = (r ^ 2)] (mod q)" 
    using cong_add by fastforce

(*----------------------end: [x * r_p * p  + x * r_q * q = x] (mod p)--------------------------------*)

  
  
  from p_cong_u2 q_cong_u2 coprime_pq
  have pq_cong: "[(?uq * r_p * p + ?up * r_q * q) = (r ^ 2)] (mod (p * q))"
    using coprime_cong_mult by fastforce
  then have nat_cong: "nat ((?uq * r_p * p + ?up * r_q * q) mod (p * q)) = nat (r ^ 2) mod (p * q)" 
    by (metis nat_int of_nat_mod  unique_euclidean_semiring_class.cong_def)

  have "r ^ 2 = nat (int (r ^ 2))" by presburger
  from this nat_cong have nat_eq: "nat ((?uq * r_p * p + ?up * r_q * q) mod (p * q)) =r ^ 2 mod (p * q)" 
    by auto
  
  from r_obtain have 
    "nat ((?uq * r_p * p + ?up * r_q * q) mod (p * q)) = 
      (let ((r_p, r_q), _) = euclid_ext p q in 
      nat ((?uq * r_p * p + ?up * r_q * q) mod (p * q)))"
  using old.prod.case
  by (metis (no_types, lifting))

  from this nat_eq 
  have let_eq: "(let ((r_p, r_q), _) = euclid_ext p q in 
      nat ((?uq * r_p * p + ?up * r_q * q) mod (p * q)))
      =r ^ 2 mod (p * q)" by algebra


  have unwrap: " (let x = r ^ (2 ^ (t + 2)) mod (p * q) in
    let u_p = x ^ (calculate_exponent t p) mod p in
    let u_q = x ^ (calculate_exponent t q) mod q in
    let ((r_p, r_q), _) = euclid_ext p q in
    nat ((u_q * r_p * p + u_p * r_q * q) mod (p * q))) = 
    (let ((r_p, r_q), _) = euclid_ext p q in
    nat ((?uq * r_p * p + ?up * r_q * q) mod (p * q)))" 
    by metis

  have "(let ((r_p, r_q), _) = euclid_ext_aux 1 0 0 1 (int p) (int q)
     in nat ((int ((r ^ 2 ^ (t + 2) mod (p * q)) ^ calculate_exponent t q mod q) * r_p * int p +
              int ((r ^ 2 ^ (t + 2) mod (p * q)) ^ calculate_exponent t p mod p) * r_q * int q) mod
             int (p * q))) = 
       (let ((r_p, r_q), _) = euclid_ext_aux 1 0 0 1 (int p) (int q)
     in nat ((int ((r ^ 2 ^ (t + 2) mod (p * q)) ^ calculate_exponent t q mod q) * r_p * int p +
              int ((r ^ 2 ^ (t + 2) mod (p * q)) ^ calculate_exponent t p mod p) * r_q * int q) mod
             int (p * q)))" by auto

  from let_eq unwrap this have "(let x = r ^ (2 ^ (t + 2)) mod (p * q) in
    let u_p = x ^ (calculate_exponent t p) mod p in
    let u_q = x ^ (calculate_exponent t q) mod q in
    let ((r_p, r_q), _) = euclid_ext p q in
    nat ((u_q * r_p * p + u_p * r_q * q) mod (p * q))) = r ^ 2 mod (p * q)" by algebra
  from this show ?thesis by fastforce
qed 


 
lemma h_not_smaller: "h \<ge> length (nat_to_words (Suc 0) (p mod 2 ^ h))"
  by (simp add: nat_bnd_word_len)

lemma length_eq: "length (nat_to_bitstring h (p mod 2^h)) = h" 
  by (auto simp add: nat_to_bitstring_def nat_to_words_len_def h_not_smaller) 


text "Here, we show that if we find the x_0, then we can recover the plaintext message 
    from encrypted message c."

lemma enc_loop_alt_correctness:
  assumes "x > 0" "n > 0" "h > 0" "x < n" 
  shows  "\<lbrakk>\<forall>l \<in> set m. length l \<le> h; c = fst (enc_loop_alt (n, h, m) x)\<rbrakk> \<Longrightarrow> 
          fst (enc_loop_alt (n, h, c) x) = m"

proof (induction m arbitrary: c x)
  case Nil
  then show ?case by auto
next
  let ?f = "nat_to_bitstring h"
  case (Cons a m)
  assume "\<forall>l \<in> set (a # m). length l \<le> h" 
  assume "c = fst (enc_loop_alt (n, h, a # m) x)"

  then have "c = enc_loop_func_list (?f, n, h, a # m) x" by auto
  then have c_def: "c = (let x_i = x * x mod n in
        let p_i = ?f (x_i mod 2^h) in
        let c_i = a [\<oplus>] p_i in
        c_i # enc_loop_func_list (nat_to_bitstring h, n, h, m) x_i
        )" by auto
  let ?a' = "(a [\<oplus>] ?f (x * x mod n mod 2^h))"

  from c_def have c_part: "c = ?a' # enc_loop_func_list (nat_to_bitstring h, n, h, m) (x * x mod n)" by metis
  then have "\<exists>c'. c = ?a' # c'" by auto
  then obtain c' where c_obtain: "c = ?a' # c'" by blast
  from this c_part have "c' = enc_loop_func_list (nat_to_bitstring h, n, h, m) (x * x mod n)" by auto
  hence "fst (enc_loop_alt (n, h, c') (x * x mod n)) = m" using Cons by auto
  hence a_with_m: "a # fst (enc_loop_alt (n, h, c') (x * x mod n)) = a # m" by auto

   have a_xor_bot: "?a' [\<oplus>] ?f (x * x mod n mod 2^h) = a [\<oplus>] (replicate (length (?f (x * x mod n mod 2^h))) bot)"
    by auto

  have "length a \<le> h" using Cons(2) by auto
  then have "a [\<oplus>] (replicate (length (?f (x * x mod n mod 2^h))) bot) = a" 
    using xor_replicate_bot_right length_eq by auto 

  from this a_xor_bot have "?a' [\<oplus>] ?f (x * x mod n mod 2^h) = a" by auto

  from this a_with_m 
  have "?a' [\<oplus>] ?f (x * x mod n mod 2^h) # fst (enc_loop_alt (n, h, c') (x * x mod n)) = a # m"
    by auto

  hence "(let x_i = x * x mod n in
        let p_i = ?f (x_i mod 2^h) in
        let c_i = ?a' [\<oplus>] p_i in
        c_i # enc_loop_func_list (nat_to_bitstring h, n, h, c') x_i
        ) = a # m" by auto
  hence "enc_loop_func_list (nat_to_bitstring h, n, h, ?a' # c') x = a # m" by auto  
  then show ?case using c_obtain by auto
qed


lemma same_length:
  shows "length (enc_loop_func_list (nat_to_bitstring h, p * q, h, m_l) x_0) = length m_l"
proof (induction m_l arbitrary: x_0)
  case Nil
  then show ?case by auto
next
  case (Cons a m_l)
  have enc_loop_open: "length (enc_loop_func_list (nat_to_bitstring h, p * q, h, a # m_l) x_0) = 
    length ((let x_i = x_0 * x_0 mod (p * q) in
        let p_i = nat_to_bitstring h (x_i mod 2^h) in
        let c_i = a [\<oplus>] p_i in
        c_i # enc_loop_func_list (nat_to_bitstring h, p * q, h, m_l) x_i
        ))" by auto
  then have "\<exists>c_i'. let x_i = x_0 * x_0 mod (p * q) in
        let p_i = nat_to_bitstring h (x_i mod 2^h) in
        c_i' = a [\<oplus>] p_i" by auto
  then obtain c_i' where obtain_c_i: "let x_i = x_0 * x_0 mod (p * q) in
        let p_i = nat_to_bitstring h (x_i mod 2^h) in
        c_i' = a [\<oplus>] p_i" by blast
  from enc_loop_open this have enc_loop_open: "length (enc_loop_func_list (nat_to_bitstring h, p * q, h, a # m_l) x_0) = 
    length (c_i' # enc_loop_func_list (nat_to_bitstring h, p * q, h, m_l) ((x_0 * x_0) mod (p * q)))" 
    by metis 
  then show ?case using Cons by auto
qed

lemma merge_split: 
  shows "h > 0 \<Longrightarrow> l = (split m h) \<Longrightarrow> merge_list l = m" 
proof (induction m h arbitrary: l rule: split.induct)
  case (1 n)
  then show ?case by auto
next
  case (2 v va)
  then show ?case by auto
next
  case (3 x xs v)
  have "split (x # xs) (Suc v) = (take (Suc v) (x # xs)) # (split (drop (Suc v) (x # xs)) (Suc v))"
    by (auto elim: split.elims)
  assume assms: "0 < Suc v" "l = split (x # xs) (Suc v)"
  then have l_def: "l =  (take (Suc v) (x # xs)) # (split (drop (Suc v) (x # xs)) (Suc v))" 
    by auto
  then have "\<exists>a l_r. l = a # l_r" by auto
  then obtain a l_r where a_l_r_obtain: "l = a # l_r" by auto
  from l_def this have "a # l_r = (take (Suc v) (x # xs)) # (split (drop (Suc v) (x # xs)) (Suc v))"
    by auto
  then have a_def: "a = (take (Suc v) (x # xs)) \<and> l_r = (split (drop (Suc v) (x # xs)) (Suc v))" 
    by auto 
  then have l_r_def: "l_r = (split (drop (Suc v) (x # xs)) (Suc v))" by auto
  
  from 3 have "0 < Suc v \<Longrightarrow>
    l_r = split (drop (Suc v) (x # xs)) (Suc v) \<Longrightarrow> merge_list l_r = drop (Suc v) (x # xs)"
    by auto
  then have " l_r = split (drop (Suc v) (x # xs)) (Suc v) 
    \<Longrightarrow> merge_list l_r = drop (Suc v) (x # xs)" using assms(1) by auto
  then have merge_l_r: "merge_list l_r = drop (Suc v) (x # xs)" using l_r_def by auto

  have "merge_list (a # l_r) = a @ merge_list l_r" using list.discI by auto
  from this merge_l_r 
  have "merge_list (a # l_r) = a @ (drop (Suc v) (x # xs))" by auto
  then have "merge_list (a # l_r) = (take (Suc v) (x # xs)) @ (drop (Suc v) (x # xs))" 
    using a_def by auto

  then show ?case  
    using a_l_r_obtain by auto
qed

corollary merge_split_in_place:
  shows "h > 0 \<Longrightarrow>  merge_list (split m h) = m" 
  using merge_split by auto


theorem correctness:
  assumes 
    "p mod 4 = 3" "q mod 4 = 3" (*pq_cong_3*)
    "prime p" "prime q" (*pq_prime*)
    "r < p * q" "m \<noteq> []"
    "coprime r (p * q)" "p \<noteq> q"
  shows "decrypt_alt p q (encrypt_alt (p * q) m r) = m"
proof - 
  from encrypt_alt_def have enc_def: "encrypt_alt (p * q) m r = (
  let h = nat \<lfloor>log 2 (log 2 (p * q))\<rfloor> in 
  let m_l = split m h in 
  let (x_0 :: nat) = (r * r) mod (p * q) in 
  let (c, x_t) = enc_loop_alt (p * q, h, m_l) x_0 in 
  let x_t' = x_t * x_t mod (p * q) in 
  (c, x_t'))"
    by auto
  then have "fst (encrypt_alt (p * q) m r) 
  = fst (let h = nat \<lfloor>log 2 (log 2 (p * q))\<rfloor> in 
  let m_l = split m h in 
  let x_0 = (r * r) mod (p * q) in enc_loop_alt (p * q, h, m_l) x_0)" 
    using prod.exhaust prod.sel(1) prod.simps(2)
    by (metis (mono_tags, lifting))

  then have "fst (encrypt_alt (p * q) m r) 
  = (let h = nat \<lfloor>log 2 (log 2 (p * q))\<rfloor> in 
  let m_l = split m h in 
  let x_0 = (r * r) mod (p * q) in fst (enc_loop_alt (p * q, h, m_l) x_0))" 
    by meson
  
  then have enc_fst_simp:  "fst (encrypt_alt (p * q) m r) 
  = (let h = nat \<lfloor>log 2 (log 2 (p * q))\<rfloor> in 
  let m_l = split m h in 
  let x_0 = (r * r) mod (p * q) in enc_loop_func_list (nat_to_bitstring h, p * q, h, m_l) x_0)"
    by auto

  have "\<exists>c. fst (encrypt_alt (p * q) m r) = c" by auto
  then obtain c where obtain_c_opt1: "fst (encrypt_alt (p * q) m r) = c" by blast
  then have obtain_c_opt2: "(let h = nat \<lfloor>log 2 (log 2 (p * q))\<rfloor> in let m_l = split m h in 
  let x_0 = (r * r) mod (p * q) in enc_loop_func_list (nat_to_bitstring h, p * q, h, m_l) x_0) = c"
    using enc_fst_simp by auto

  from enc_def have "snd (encrypt_alt (p * q) m r) 
  = snd (let h = nat \<lfloor>log 2 (log 2 (p * q))\<rfloor> in 
  let m_l = split m h in 
  let x_0 = (r * r) mod (p * q) in 
  let (c, x_t) = enc_loop_alt (p * q, h, m_l) x_0 in 
  let x_t' = x_t * x_t mod (p * q) in 
  (c, x_t'))" 
    by auto

  then have  "snd (encrypt_alt (p * q) m r) 
  = (let h = nat \<lfloor>log 2 (log 2 (p * q))\<rfloor> in 
  let m_l = split m h in 
  let x_0 = (r * r) mod (p * q) in 
  let x_t = snd (enc_loop_alt (p * q, h, m_l) x_0) in 
  let x_t' = x_t * x_t mod (p * q) in 
  x_t')" 
    by (smt (verit, ccfv_SIG) case_prod_unfold prod.sel(2))

  then have  "snd (encrypt_alt (p * q) m r) 
  = (let h = nat \<lfloor>log 2 (log 2 (p * q))\<rfloor> in 
  let m_l = split m h in 
  let x_0 = (r * r) mod (p * q) in 
  let x_t = enc_loop_func_x (nat_to_bitstring h, p * q, h, length m_l) x_0 in 
  let x_t' = x_t * x_t mod (p * q) in 
  x_t')" by auto

  then have "snd (encrypt_alt (p * q) m r) 
  = (let h = nat \<lfloor>log 2 (log 2 (p * q))\<rfloor> in 
  let m_l = split m h in 
  let x_0 = (r * r) mod (p * q) in 
  let x_t = x_0 ^ (2 ^ (length m_l)) mod (p * q) in 
  let x_t' = x_t * x_t mod (p * q) in 
  x_t')" by auto

  then have snd_open: "snd (encrypt_alt (p * q) m r) 
  = (let h = nat \<lfloor>log 2 (log 2 (p * q))\<rfloor> in 
  let m_l = split m h in  
  ((((r * r) mod (p * q)) ^ (2 ^ (length m_l)) mod (p * q)) 
* (((r * r) mod (p * q)) ^ (2 ^ (length m_l)) mod (p * q)))) mod (p * q)" 
    by metis

  have "[(let h = nat \<lfloor>log 2 (log 2 (p * q))\<rfloor> in 
  let m_l = split m h in  
  ((((r * r) mod (p * q)) ^ (2 ^ (length m_l)) mod (p * q)) 
* (((r * r) mod (p * q)) ^ (2 ^ (length m_l)) mod (p * q)))) mod (p * q)
   = (let h = nat \<lfloor>log 2 (log 2 (p * q))\<rfloor> in 
  let m_l = split m h in  
  (r * r) ^ (2 ^ (length m_l))
* (r * r) ^ (2 ^ (length m_l)))] (mod (p * q))" 
  by (metis (no_types, opaque_lifting) cong_mod_left cong_refl power2_eq_square power_mod)


  from this snd_open  have "snd (encrypt_alt (p * q) m r) 
  = (let h = nat \<lfloor>log 2 (log 2 (p * q))\<rfloor> in 
  let m_l = split m h in  
  (r * r) ^ (2 ^ (length m_l))
  * (r * r) ^ (2 ^ (length m_l))) mod (p * q)" 
    by (metis power2_eq_square power_mod)

  then have "snd (encrypt_alt (p * q) m r) 
  = (let h = nat \<lfloor>log 2 (log 2 (p * q))\<rfloor> in 
  let m_l = split m h in  
  ((r * r) ^ (2 ^ (length m_l) + 2 ^ (length m_l))))
   mod (p * q)" using power_add[symmetric]
    by metis

   then have "snd (encrypt_alt (p * q) m r) 
  = (let h = nat \<lfloor>log 2 (log 2 (p * q))\<rfloor> in 
  let m_l = split m h in  
  ((r * r) ^ (2 * 2 ^ (length m_l))))
   mod (p * q)" using mult_2[symmetric]
     by metis

  
   then have snd_eq: "snd (encrypt_alt (p * q) m r) 
  = (let h = nat \<lfloor>log 2 (log 2 (p * q))\<rfloor> in 
  let m_l = split m h in  
  (r * r) ^ (2 ^ (Suc (length m_l))))
   mod (p * q)" by auto

  then have "\<exists>h. h = nat \<lfloor>log 2 (log 2 (p * q))\<rfloor>" by auto
  then obtain h where  h_obtain: "h = nat \<lfloor>log 2 (log 2 (p * q))\<rfloor>" by blast

  have "\<exists>x. x = snd (encrypt_alt (p * q) m r)" by auto
  then obtain x where obtain_x_opt1: "x = snd (encrypt_alt (p * q) m r)" by blast

  
  from h_obtain have "snd (encrypt_alt (p * q) m r) = (r * r) ^ (2 ^ (Suc (length (split m h)))) mod (p * q)"
    using snd_eq by presburger
  then have "snd (encrypt_alt (p * q) m r) = (r ^ 2) ^ (2 ^ (Suc (length (split m h)))) mod (p * q)" 
    using power2_eq_square[symmetric] by metis
  then have "snd (encrypt_alt (p * q) m r) = r ^ (2 ^ ((length (split m h)) + 2)) mod (p * q)"
    by (auto simp add: power_mult)
  then have obtain_x_opt2: "x =  r ^ (2 ^ ((length (split m h)) + 2)) mod (p * q)" 
    using obtain_x_opt1 by auto

  from obtain_c_opt2 h_obtain 
  have obtain_c_opt3: "c = enc_loop_func_list (nat_to_bitstring h, p * q, h, (split m h)) (r * r mod (p * q))" 
    by metis

  from assms(1) assms(2) assms(3) assms(4) assms(5) assms(7) assms(8)
      same_x_0
  have x_0_eq: "(let x = r ^ 2 ^ (length (split m h) + 2) mod (p * q); 
         u_p = x ^ calculate_exponent (length (split m h)) p mod p;
         u_q = x ^ calculate_exponent (length (split m h)) q mod q;
         ((r_p, r_q), _) = euclid_ext_aux 1 0 0 1 (int p) (int q)
         in
         nat ((int u_q * r_p * int p + int u_p * r_q * int q) mod int (p * q))) =
         r ^ 2 mod (p * q)" by blast
  
  from same_length obtain_c_opt2 
  have "length (enc_loop_func_list (nat_to_bitstring h, p * q, h, (split m h)) (r * r mod (p * q)))
     = length (split m h)" 
    by auto
  from this obtain_c_opt3 have length_eq: "length c = length (split m h)" by auto
  from length_eq obtain_x_opt2 have obtain_x_opt3: "x = r ^ 2 ^ (length c + 2) mod (p * q)" by auto


  from length_eq x_0_eq have x_0_eqc: "(let x = r ^ 2 ^ (length c + 2) mod (p * q);
         u_p = x ^ calculate_exponent (length c) p mod p;
         u_q = x ^ calculate_exponent (length c) q mod q;
         ((r_p, r_q), _) = euclid_ext (int p) (int q)
         in
         nat ((int u_q * r_p * int p + int u_p * r_q * int q) mod int (p * q))) =
         r ^ 2 mod (p * q)" by algebra


  then have "(let u_p = x ^ calculate_exponent (length c) p mod p;
         u_q = x ^ calculate_exponent (length c) q mod q;
         ((r_p, r_q), _) = euclid_ext (int p) (int q)
         in
         nat ((int u_q * r_p * int p + int u_p * r_q * int q) mod int (p * q))) =
         r ^ 2 mod (p * q)" using obtain_x_opt3 by meson

  then have "(let ((r_p, r_q), _) = euclid_ext (int p) (int q) in
         nat ((int (x ^ calculate_exponent (length c) q mod q) * r_p * int p 
        + int (x ^ calculate_exponent (length c) p mod p) * r_q * int q) mod int (p * q))) =
         r ^ 2 mod (p * q)" by algebra

  then have all_collapsed: "nat ((int (x ^ calculate_exponent (length c) q mod q) * fst (fst (euclid_ext (int p) (int q))) * int p 
        + int (x ^ calculate_exponent (length c) p mod p) * snd (fst (euclid_ext (int p) (int q))) * int q) mod int (p * q)) =
         r ^ 2 mod (p * q) " 
    by (metis (no_types, lifting) case_prod_conv prod.collapse)


  have "decrypt_alt p q (encrypt_alt (p * q) m r) = decrypt_alt p q (c, x)"
    using obtain_c_opt1 obtain_x_opt1 by auto

  also have "... =
    (case (c, x) of (c, x) \<Rightarrow>
       let u_p = x ^ calculate_exponent (length c) p mod p; 
           u_q = x ^ calculate_exponent (length c) q mod q;
           ((r_p, r_q), _) = euclid_ext (int p) (int q);
           x_0 = nat ((int u_q * r_p * int p + int u_p * r_q * int q) mod int (p * q));
           (m, x') = enc_loop_alt (p * q, nat \<lfloor>log 2 (log 2 (p * q))\<rfloor>, c) x_0
       in merge_list m)" using decrypt_alt_def by force

  ultimately have "decrypt_alt p q (encrypt_alt (p * q) m r) = 
    (let u_p = x ^ (calculate_exponent (length c) p) mod p;
         u_q = x ^ (calculate_exponent (length c) q) mod q;
         ((r_p, r_q), _) = euclid_ext p q; 
         x_0 = nat ((u_q * r_p * p + u_p * r_q * q) mod (p * q));
        (m, x') = enc_loop_alt (p * q, (nat h) , c) x_0 in
         merge_list m)" using h_obtain by auto

  
  then have "decrypt_alt p q (encrypt_alt (p * q) m r) = 
    (let ((r_p, r_q), _) = euclid_ext p q; 
         x_0 = nat (((x ^ (calculate_exponent (length c) q) mod q) * r_p * p 
        + (x ^ (calculate_exponent (length c) p) mod p) * r_q * q) mod (p * q));
        (m, x') = enc_loop_alt (p * q, (nat h) , c) x_0 in
         merge_list m)"
    by algebra

  then have  "decrypt_alt p q (encrypt_alt (p * q) m r) = 
    (let 
         x_0 = nat (((x ^ (calculate_exponent (length c) q) mod q) * fst (fst (euclid_ext (int p) (int q))) * p 
        + (x ^ (calculate_exponent (length c) p) mod p) * snd (fst (euclid_ext (int p) (int q))) * q) mod (p * q));
        (m, x') = enc_loop_alt (p * q, (nat h) , c) x_0 in
         merge_list m)" 
    by (metis (no_types, lifting) case_prod_conv prod.collapse)

  then have  "decrypt_alt p q (encrypt_alt (p * q) m r) =  (let 
         x_0 = r ^ 2 mod (p * q);
        (m, x') = enc_loop_alt (p * q, (nat h) , c) x_0 in
         merge_list m)" using all_collapsed by algebra
  then have decrypt_eq_merge: "decrypt_alt p q (encrypt_alt (p * q) m r) = 
    merge_list (fst (enc_loop_alt (p * q, (nat h) , c) (r ^ 2 mod (p * q))))" by auto

  from assms(1,2,3,4) have pq_greater_zero: "p * q > 0" by auto
  then have p_greater_zero: "p > 0" by auto
  from pq_greater_zero have q_greater_zero: "q > 0" by auto

  have not_prime_1: "\<not> prime 1" by auto
  then have p_noteq_1: "p \<noteq> 1" using assms(3) by auto
  from not_prime_1 have q_noteq_1: "q \<noteq> 1" using assms(4) by auto
  from assms(1) have p_noteq_2: "p \<noteq> 2" by linarith
  from assms(2) have q_noteq_2:"q \<noteq> 2" by linarith
  from p_noteq_1 p_noteq_2 p_greater_zero have p_gr_2: "p > 2" by auto
  from q_noteq_1 q_noteq_2 q_greater_zero have q_gr_2: "q > 2" by auto

  from p_gr_2 q_gr_2 have "p * q > 2 * 2" 
    using mult_strict_mono by blast
  then have "p * q > 2 ^ 2" by auto
  then have "log 2 (p * q) > 2" 
    using Multiseries_Expansion.intyness_simps(6) less_log2_of_power by presburger
  then have "log 2 (log 2 (p * q)) > 1" by auto
  then have "\<lfloor>log 2 (log 2 (real (p * q)))\<rfloor> \<ge> 1" by auto
  then have "nat \<lfloor>log 2 (log 2 (real (p * q)))\<rfloor> \<ge> 1" 
    by (simp add: le_simps(3))
  then have h_gr_1: "h \<ge> 1" using h_obtain by auto
  
  from this assms(7,8) have "r \<noteq> 0" 
    using coprime_crossproduct_nat coprime_mult_right_iff mult_eq_if
    by (metis)
  then have "r > 0" by auto
  
  from this assms have x_gr_0: "r ^ 2 mod (p * q) > 0" 
    by (auto simp add: coprime_commute coprime_dvd_mult_left_iff mod_greater_zero_iff_not_dvd 
                       nat_dvd_not_less power2_eq_square)
  
  have x_less_n: "r ^ 2 mod (p * q) < p * q" 
    using mod_less_divisor pq_greater_zero by blast 

  from split_l have split_set: "\<forall>l\<in>set (split m h). length l \<le> h" by auto

  from x_gr_0 pq_greater_zero h_gr_1 x_less_n split_set enc_loop_alt_correctness 
  have "c = fst (enc_loop_alt (p * q, h, (split m h)) (r ^ 2 mod (p * q))) \<Longrightarrow> 
        fst (enc_loop_alt (p * q, (nat h), c) (r ^ 2 mod (p * q))) = (split m (nat h))" by auto

  then have "c = (enc_loop_func_list (nat_to_bitstring h, p * q, h, (split m h)) (r ^ 2 mod (p * q))) \<Longrightarrow> 
        fst (enc_loop_alt (p * q, (nat h), c) (r ^ 2 mod (p * q))) = (split m (nat h))" by auto

  then have "fst (enc_loop_alt (p * q, (nat h), c) (r ^ 2 mod (p * q))) = (split m (nat h))" 
    using obtain_c_opt3 power2_eq_square[symmetric] by metis
  
  then have decrypt_merge: "decrypt_alt p q (encrypt_alt (p * q) m r) = 
    merge_list ((split m (nat h)))" using decrypt_eq_merge by auto

  from h_gr_1 have "merge_list ((split m (nat h))) = m" 
     using merge_split_in_place by auto

  from this decrypt_merge show ?thesis by auto (*what? did i really finish it now???*)
 qed


 text "Showing the equivalence of \<open>enc_loop\<close> and \<open>enc_loop_alt\<close>, which splits the job into two different 
 functions, \<open>enc_loop_func_x\<close> and \<open>enc_loop_func_list\<close>."

lemma enc_loop_func_exp: 
  assumes "n > 0" "x < n"
  shows "snd (enc_loop_func (nat_to_bitstring h, n, h, m) c x) = x ^ (2 ^ (length m)) mod n"
  using assms
proof (induction m arbitrary: x c)
  case Nil
  then have "(enc_loop_func (nat_to_bitstring h, n, h, []) c x) = (rev c, x)" using enc_loop_func.simps(1) by auto
  then show ?case using local.Nil(2) by auto
next
  case (Cons a m)
  then have enc_loop_def: "snd (enc_loop_func (nat_to_bitstring h, n, h, (a # m)) c x) = snd(
        (let x_i = x * x mod n in
        let p_i = (nat_to_bitstring h) (x_i mod 2^h) in
        let c_i = a [\<oplus>] p_i in
        enc_loop_func ((nat_to_bitstring h), n, h, m) (c_i # c) x_i))" using enc_loop_func.simps by auto

  from mod_less_divisor assms(1) have "x * x mod n < n" by auto
  
  from this enc_loop_def Cons.IH assms(1) assms(2) 
  have use_ia: "snd (enc_loop_func (nat_to_bitstring h, n, h, (a # m)) c x) = (x * x mod n) ^ (2 ^ length m) mod n"
    by metis

  have "(x * x) ^ (2 ^ length m) mod n = (x * x mod n) ^ (2 ^ length m) mod n"  
    using power_mod[symmetric] by auto
  from use_ia this have x_times_x:  "snd (enc_loop_func (nat_to_bitstring h, n, h, (a # m)) c x) = (x * x) ^ (2 ^ length m) mod n" 
    by auto

  have "(x * x) ^ (2 ^ length m) = x ^ (2 ^ length (a # m))"
    by (auto simp add: power2_eq_square power_mult) 
  from this x_times_x show ?case by auto
qed

corollary enc_loop_x: 
  assumes "n > 0" "x < n"
  shows "snd (enc_loop_func (nat_to_bitstring h, n, h, m) c x) = snd (enc_loop_alt (n, h, m) x)"
  by (auto intro: enc_loop_func_exp simp add: assms)

corollary enc_loop_x_enc_loop_normal: 
  assumes "n > 0" "x < n"
  shows "snd (enc_loop (n, h, m) x) = snd (enc_loop_alt (n, h, m) x)"
  by (auto intro: enc_loop_func_exp simp add: assms)

corollary enc_loop_exp: 
  assumes "n > 0" "h > 0" "x < n"
  shows "snd (enc_loop (n, h, m) x) = x ^ (2 ^ (length m)) mod n"
  by (auto intro: enc_loop_func_exp simp add: assms)

theorem enc_x_exp: 
  assumes "n > 0" "r < n" "h = nat \<lfloor>log 2 (log 2 n)\<rfloor>" "m_l = split m h"
  shows "snd (encrypt n m r) = (r * r) ^ (2 ^ (length m_l + 1)) mod n"
proof - 
  from encrypt_def have encrypt_open: "snd (encrypt n m r) = snd (
  let h = nat \<lfloor>log 2 (log 2 n)\<rfloor> in 
  let m_l = split m h in 
  let (x_0 :: nat) = (r * r) mod n in 
  let (c, x_t) = enc_loop (n, h, m_l) x_0 in 
  let x_t' = x_t * x_t mod n in 
  (c, x_t'))" by auto
  
  have "r * r mod n < n" using mod_less_divisor assms(1) by auto

  then have  "snd (
  let h = nat \<lfloor>log 2 (log 2 n)\<rfloor> in 
  let m_l = split m h in 
  let (x_0 :: nat) = (r * r) mod n in 
  enc_loop (n, h, m_l) x_0) = 
  (let h = nat \<lfloor>log 2 (log 2 n)\<rfloor> in 
  let m_l = split m h in 
  let (x_0 :: nat) = (r * r) mod n in 
  (x_0 ^ (2 ^ (length m_l)) mod n))" using assms(1) enc_loop.simps enc_loop_func_exp
    by (metis)
  from encrypt_open this have "snd (
  let h = nat \<lfloor>log 2 (log 2 n)\<rfloor> in 
  let m_l = split m h in 
  let (x_0 :: nat) = (r * r) mod n in 
  let (c, x_t) = enc_loop (n, h, m_l) x_0 in 
  let x_t' = x_t * x_t mod n in 
  (c, x_t'))
  = 
  (let h = nat \<lfloor>log 2 (log 2 n)\<rfloor> in 
  let m_l = split m h in 
  let (x_0 :: nat) = (r * r) mod n in 
  let x_t' = x_0 ^ (2 ^ (length m_l)) mod n in 
  x_t' * x_t' mod n)" 
  using old.prod.exhaust snd_conv split_conv
  by (smt (verit, best)) 

  then have  "snd (
  let h = nat \<lfloor>log 2 (log 2 n)\<rfloor> in 
  let m_l = split m h in 
  let (x_0 :: nat) = (r * r) mod n in 
  let (c, x_t) = enc_loop (n, h, m_l) x_0 in 
  let x_t' = x_t * x_t mod n in 
  (c, x_t'))
  = 
  (((r * r) mod n) ^ (2 ^ (length m_l)) mod n) * (((r * r) mod n) ^ (2 ^ (length m_l)) mod n) mod n" 
  using assms 
  by meson

  then have "snd (encrypt n m r) = (((r * r) mod n) ^ (2 ^ (length m_l)) mod n) * (((r * r) mod n) ^ (2 ^ (length m_l)) mod n) mod n" 
    using encrypt_open by auto
  then have "snd (encrypt n m r) = ((r * r) ^ (2 ^ (length m_l)) mod n) * ((r * r) ^ (2 ^ (length m_l)) mod n) mod n"
    using power_mod by metis
  then have encrypt_to_exp: "snd (encrypt n m r) = (((r * r) ^ (2 ^ (length m_l))) * ((r * r) ^ (2 ^ (length m_l)))) mod n"
    by (simp add: mod_mult_eq) 

  have "(((r * r) ^ (2 ^ (length m_l))) * ((r * r) ^ (2 ^ (length m_l)))) = (r * r) ^ (2 ^ (length m_l) + 2 ^ (length m_l))" 
    using power_add[symmetric] by auto
  then have "(((r * r) ^ (2 ^ (length m_l))) * ((r * r) ^ (2 ^ (length m_l)))) = (r * r) ^ (2 * 2 ^ (length m_l))"
    by (simp add: mult_2)
  then have "(((r * r) ^ (2 ^ (length m_l))) * ((r * r) ^ (2 ^ (length m_l)))) = (r * r) ^ (2 ^ (length m_l + 1))"
    by auto
  from this encrypt_to_exp show ?thesis by auto
qed

lemma fst_enc_loop_eq_enc_between: "fst (enc_loop_func (f, n, h, m) c_acc x) = enc_loop_func_between (f, n, h, m) c_acc x"
proof (induction m arbitrary: x c_acc)
  case (Nil)
  then show ?case by auto
next
  case (Cons a m)
  have "fst (enc_loop_func (f, n, h, (a # m)) c_acc x) = fst (let x_i = x * x mod n in
        let p_i = f (x_i mod 2^h) in
        let c_i = a [\<oplus>] p_i in
        enc_loop_func (f, n, h, m) (c_i # c_acc) x_i
        )"  
    by auto
  then have "fst (enc_loop_func (f, n, h, (a # m)) c_acc x) = (let x_i = x * x mod n in
        let p_i = f (x_i mod 2^h) in
        let c_i = a [\<oplus>] p_i in
        fst (enc_loop_func (f, n, h, m) (c_i # c_acc) x_i)
        )" unfolding Let_def by auto
  then have  "fst (enc_loop_func (f, n, h, (a # m)) c_acc x) = (let x_i = x * x mod n in
        let p_i = f (x_i mod 2^h) in
        let c_i = a [\<oplus>] p_i in
        enc_loop_func_between (f, n, h, m) (c_i # c_acc) x_i
        )" using Cons by auto
  then show ?case by auto
qed 

lemma enc_betw_eq_enc_list:"enc_loop_func_between (f, n, h, m) c_acc x = rev c_acc @ (enc_loop_func_list (f, n, h, m) x)"
proof (induction m arbitrary: x c_acc)
  case Nil
  then show ?case by auto
next
  case (Cons a m)
  let ?c_i = "a [\<oplus>] f ((x * x mod n) mod 2^h)"
  let ?x_i = "x * x mod n"
  have "enc_loop_func_between (f, n, h, a # m) c_acc x =  (let x_i = x * x mod n in
        let p_i = f (x_i mod 2^h) in
        let c_i = a [\<oplus>] p_i in
        enc_loop_func_between (f, n, h, m) (c_i # c_acc) x_i
        )" by auto
  hence "enc_loop_func_between (f, n, h, a # m) c_acc x = enc_loop_func_between (f, n, h, m) (?c_i # c_acc) ?x_i" 
    unfolding Let_def by auto
  hence "enc_loop_func_between (f, n, h, a # m) c_acc x = rev (?c_i # c_acc) @ enc_loop_func_list (f, n, h, m) ?x_i" 
    using Cons by auto
  hence "enc_loop_func_between (f, n, h, a # m) c_acc x = rev c_acc @ [?c_i] @ enc_loop_func_list (f, n, h, m) ?x_i"
    using rev_def by auto
  hence enc_loop_betw_def: "enc_loop_func_between (f, n, h, a # m) c_acc x = rev c_acc @ (?c_i # enc_loop_func_list (f, n, h, m) ?x_i)"
    by auto
  have "enc_loop_func_list (f, n, h, a # m) x = (let x_i = x * x mod n in
        let p_i = f (x_i mod 2^h) in
        let c_i = a [\<oplus>] p_i in
        c_i # enc_loop_func_list (f, n, h, m) x_i
        )" by auto
  hence "enc_loop_func_list (f, n, h, a # m) x = ?c_i # enc_loop_func_list (f, n, h, m) (x * x mod n)"
    unfolding Let_def by auto   
  thus ?case  using enc_loop_betw_def unfolding Let_def by auto
qed

corollary fst_enc_eq_enc_list: "fst (enc_loop_func (f, n, h, m) [] x) = enc_loop_func_list (f, n, h, m) x" 
  using enc_betw_eq_enc_list fst_enc_loop_eq_enc_between by auto

corollary 
  assumes "0 < n" "x < n"
  shows "enc_loop (n, h, m) x = enc_loop_alt (n, h, m) x"
  using enc_loop_x_enc_loop_normal fst_enc_eq_enc_list 
proof - 
  have "snd (enc_loop (n, h, m) x) = snd (enc_loop_func (nat_to_bitstring h, n, h, m) [] x)" 
    by auto
  then have snd_eq: "snd (enc_loop (n, h, m) x) = snd (enc_loop_alt (n, h, m) x)" 
    using assms enc_loop_x_enc_loop_normal by auto

  have "fst (enc_loop (n, h, m) x) = fst (enc_loop_func (nat_to_bitstring h, n, h, m) [] x)" 
    by auto
  then have "fst (enc_loop (n, h, m) x) = enc_loop_func_list (nat_to_bitstring h, n, h, m) x"
    using fst_enc_eq_enc_list by auto
  then have fst_eq: "fst (enc_loop (n, h, m) x) = fst (enc_loop_alt (n, h, m) x)" by auto

  from fst_eq snd_eq show "?thesis" 
    using prod.expand by blast 
qed 
end