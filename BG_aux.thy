theory BG_aux 
imports Sigma_Commit_Crypto.Number_Theory_Aux 
begin 

section "Auxillary Lemmas"

text "Here, we have all the auxillary definitions used in the formalization of Blum-Goldwasser cryptosystem"


section "Auxillary Lemmas"

text "Here, we have all the auxillary lemmas used to prove the correctness of Blum-Goldwasser cryptosystem"


text "Out proof of correctness will only consider x_i that are squared in modulo residue of p. We 
Therefore prove that case only:"
lemma eulers_criterion:
  assumes "prime (p :: nat)" "odd p" "coprime p x" "(\<exists>y. [y^2 = x] (mod p))"
  shows "[x^((p - 1) div 2) = 1] (mod p)"
proof -
  from assms(2) have even_p_minus_one: "even (p - 1)" by auto
  then have "(\<exists>k. p - 1 = 2 * k)"  by blast
  then obtain k where obtain_k:"p - 1 = 2 * k" by blast
  from assms(1) assms(3) have "\<not> p dvd x"  by auto
  from this assms(1) fermat_theorem 
  have "[x^(p - 1) = 1] (mod p)"
    by algebra
  then have "[x^((p - 1) div 2) * x^((p - 1) div 2) = 1] (mod p)" 
  using dvd_div_mult_self even_p_minus_one power2_eq_square power_mult
  by (metis)
  then have trial: "[x^((p - 1) div 2) = 1] (mod p) \<or> [x^((p - 1) div 2) = -1] (mod p)" 
    using assms(1) cong_int_iff cong_square int_ops(2) mult_0_right nat_code(2) nat_int
      negative_zle of_nat_mult prime_nat_int_transfer
    by (smt (z3) )

  from assms(4) obtain y where obtain_y: "[y^2 = x] (mod p)" by blast
  from trial obtain_y have options: "[(y^2)^((p - 1) div 2) = 1] (mod p) \<or> [(y^2)^((p - 1) div 2) = -1] (mod p)"
  using cong_int_iff cong_pow cong_trans
    by (meson)
  have "\<not> [(y^2)^((p - 1) div 2) = -1] (mod p)" 
  proof (rule ccontr)
    assume "\<not> \<not> [(y^2)^((p - 1) div 2) = -1] (mod p)"
    then have "[(y^2)^((p - 1) div 2) = -1] (mod p)" by auto
    then have "[(y)^(((p - 1) div 2) * 2) = -1] (mod p)" using power_mult
      by (metis mult.commute)
    then have y_minus_one: "[(y)^(p - 1) = -1] (mod p)"
      using even_p_minus_one by auto

    have "\<not> p dvd y" 
      using \<open>\<not> p dvd x\<close> assms(1) cong_dvd_iff obtain_y pos2 prime_dvd_power_nat_iff by blast

    then have "[(y)^(p - 1) = 1] (mod p)"
      using fermat_theorem assms(1) by auto
    from this y_minus_one have contradiction: "[(y)^(p - 1) = -1] (mod p) \<and> [(y)^(p - 1) = 1] (mod p)" by auto

    then have "[-1 = (y)^(p - 1)] (mod p) \<and> [(y)^(p - 1) = 1] (mod p)" 
      using cong_sym_eq by auto
    then have "[-1 = (y)^(p - 1)] (mod p) \<and> [int (y)^(p - 1) = int 1] (mod p)" 
      using cong_int_iff int_ops(2) by force
    then have "[-1 = 1] (mod p)" using cong_trans by auto
    then have "[1 = -1] (mod p)" using cong_sym by auto
    then have "p dvd (1 - (-1))" using cong_iff_dvd_diff 
      by fast
    then have "p dvd 2" by presburger
    thus "False" 
       using assms(2) assms(1) primes_dvd_imp_eq two_is_prime_nat by blast
  qed
   
  from this options have "[(y^2)^((p - 1) div 2) = 1] (mod p)" by auto
  thus ?thesis using obtain_y cong_pow cong_sym cong_trans
    by (meson)
qed

(*TODO: Get rid of all meson/smt/metis calls!!*)





text "Proof that (\<lfloor>log 2 (log 2 n)\<rfloor> can be rewritten as \<lfloor>log 2 \<lfloor>log 2 n\<rfloor>\<rfloor>"

lemma 
  assumes "(n::nat) > 2"
  shows "\<And>(k::nat). (\<lfloor>log 2 (log 2 n)\<rfloor> = k) = (\<lfloor>log 2 \<lfloor>log 2 n\<rfloor>\<rfloor> = k)" 
proof -
   have log_n_greater_zero: "(log 2 n) > 0" using assms by auto
  then have floor_log: "\<And>(k::nat). (\<lfloor>log 2 (log 2 n)\<rfloor> = k) = (2 ^ k \<le> log 2 n \<and> log 2 n < 2 ^ (Suc k))"  
    using assms floor_log_eq_powr_iff powr_realpow 
          Num.of_nat_simps(4) int_ops(2) of_int_of_nat_eq
    by (smt (verit, best) of_nat_Suc)

  also have log_n_greater_zero: "(log 2 n) > 0" using assms by auto
  then have floor2: "\<And>(k::nat). (\<lfloor>log 2 \<lfloor>log 2 n\<rfloor>\<rfloor> = k) = (2 ^ k \<le> real_of_int \<lfloor>log 2 n\<rfloor> \<and> real_of_int \<lfloor>log 2 n\<rfloor> < 2 ^ (Suc k))"  
    using assms floor_log_eq_powr_iff powr_realpow 
          Num.of_nat_simps(4) int_ops(2) of_int_of_nat_eq
    by (smt (verit) nat_1_add_1 nat_less_real_le of_int_0_less_iff 
        of_int_add of_nat_1 one_le_log_cancel_iff plus_1_eq_Suc zero_less_floor)

  then have "\<And>(k::nat). (2 ^ k \<le> log 2 n) = (2 ^ k \<le> \<lfloor>log 2 n\<rfloor>)" 
    by (simp add: le_floor_iff)
  
  from floor_log this
  have floor_down: "\<And>(k::nat). (\<lfloor>log 2 (log 2 n)\<rfloor> = k) = (2 ^ k \<le> \<lfloor>log 2 n\<rfloor> \<and> \<lfloor>log 2 n\<rfloor> < 2 ^(Suc k))"
    using not_less 
  by (smt (verit) of_int_1 of_int_add)
 
  from assms have "\<lfloor>log 2 n\<rfloor> > 0" by auto
  from this floor_down floor2 show "\<And>(k::nat). (\<lfloor>log 2 (log 2 n)\<rfloor> = k) = (\<lfloor>log 2 \<lfloor>log 2 n\<rfloor>\<rfloor> = k)" 
    using numeral_power_le_of_int_cancel_iff of_int_less_numeral_power_cancel_iff by blast
qed

end