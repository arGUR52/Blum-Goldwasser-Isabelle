theory BG_prob imports
  Main
  BG_aux
  BG_formalization
  BG_correctness
begin

section "Formalization of Blum-Goldwasser cryptosystem in a probabilistic setting"

type_synonym pub_key = nat
type_synonym priv_key = "nat \<times> nat"

subsection "Key generation"

text "We generate a key by uniformally sampling a set of natural numbers that are congruent to 3 
modulo 4. To ensure that \<open>p \<noteq> q\<close>, we remove the first selected number from the sample set."
definition key_gen_prob :: "nat \<Rightarrow> nat \<Rightarrow> (pub_key \<times> priv_key) pmf"
where 
  "key_gen_prob lower upper = do {
    let \<K> = {(p::nat). prime p \<and>  p mod 4 = 3 \<and> lower \<le> p \<and> p \<le> upper};
    p \<leftarrow> pmf_of_set \<K>; 
    q \<leftarrow> pmf_of_set (\<K> - {p});
    return_pmf (key_gen p q)
  }"


lemma 
  assumes "finite \<K>" "card \<K> > 1"
  shows "pmf (pmf_of_set (\<K> \<times> \<K> - {(x, x) |x. x \<in> \<K>})) (p, q) 
   = pmf (do {
    p \<leftarrow> pmf_of_set \<K>; 
    q \<leftarrow> pmf_of_set (\<K> - {p});
    return_pmf (p, q)}) (p, q)"
proof - 
  from assms(2) have card_\<K>: "card \<K> \<ge> 2" by auto
  let ?id = "{p. \<exists>x. p = (x, x) \<and> x \<in> \<K>}"
  from assms(1) have finite_\<K>_pair: "finite (\<K> \<times> \<K>)" by auto
  then have end_set_finite: "finite (\<K> \<times> \<K> - ?id)" by auto

  have card_\<K>_pair: "card (\<K> \<times> \<K>) = card \<K> * card \<K>" 
    by (simp add: card_cartesian_product)
  have id_subset: "?id \<subseteq> \<K> \<times> \<K>" by auto
  then have finite_id: "finite ?id" using finite_subset finite_\<K>_pair by auto

  let ?double = "\<lambda>x. (x, x)"
  
  have inj_on_\<K>: "inj_on ?double \<K>"
    using inj_on_convol_ident
    by fast
  have "?double ` \<K> = ?id" 
    by auto
  then have card_id: "card \<K> = card ?id"
    using inj_on_\<K> card_image 
    by fastforce
  
  have  "card ((\<K> \<times> \<K>) - ?id) = card (\<K> \<times> \<K>) - card ?id"
    using id_subset card_Diff_subset finite_id
    by auto
  then have "card ((\<K> \<times> \<K>) - ?id) = card \<K> * card \<K> - card \<K>"
    using card_\<K>_pair card_id by auto
  then have card_times_id: "card ((\<K> \<times> \<K>) - ?id) = card \<K> * (card \<K> - 1)"
    using nat_distrib(4) nat_mult_1_right by presburger
  then have "card ((\<K> \<times> \<K>) - ?id) \<ge> 2 * (2 - 1)" 
    using card_\<K>
    using diff_le_mono mult_le_mono by presburger
  then have "card ((\<K> \<times> \<K>) - ?id) \<ge> 2" by auto
  then have end_set_not_empty: "(\<K> \<times> \<K>) - ?id \<noteq> {}" by fastforce

  from end_set_not_empty pmf_of_set
  have "pmf (pmf_of_set (\<K> \<times> \<K> - ?id)) (p, q) = indicator (\<K> \<times> \<K> - ?id) (p, q) / (card (\<K> \<times> \<K> - ?id))" 
    by (simp add: end_set_finite)
  then have left_side_final: "pmf (pmf_of_set (\<K> \<times> \<K> - ?id)) (p, q) = indicator (\<K> \<times> \<K> - ?id) (p, q) / (card \<K> * (card \<K> - 1))"
    using card_times_id by auto


  let ?pmf_fun = "\<lambda>xa. do {q \<leftarrow> pmf_of_set (\<K> - {xa}); return_pmf (xa, q)}"
  let ?pmf_whole = "pmf (do {
    p \<leftarrow> pmf_of_set \<K>; 
    q \<leftarrow> pmf_of_set (\<K> - {p});
    return_pmf (p, q)})"
  
  from assms(2) have "\<K> \<noteq> {}" by auto
  from this assms(2)
  have pmf_bind_1: "?pmf_whole (p, q) = (\<Sum>xa\<in>\<K>. pmf (?pmf_fun xa) (p, q)) / real (card \<K>)"
    using assms
    by (auto simp add: pmf_bind_pmf_of_set)

  have finite_minus: "\<And>p. finite (\<K> - {p})" using assms(1) by auto
  have  "\<And>p. card (\<K> - {p}) > 0" using assms(2) 
    by (simp add: \<open>\<K> \<noteq> {}\<close> assms(1) card_Diff_singleton_if)
  then have not_empty_minus: "\<And>p. (\<K> - {p}) \<noteq> {}" 
   using card_gt_0_iff by blast

  have "(\<Sum>xa\<in>\<K>. pmf (?pmf_fun xa) (p, q)) = 
    (\<Sum>xa\<in>\<K>. (\<Sum>xb\<in>(\<K> - {xa}). pmf (return_pmf (xa, xb)) (p, q)) / real (card (\<K> - {xa})))"
    using finite_minus not_empty_minus
    by (auto simp add: pmf_bind_pmf_of_set)

  then have "(\<Sum>xa\<in>\<K>. pmf (?pmf_fun xa) (p, q)) =
    (\<Sum>xa\<in>\<K>. (\<Sum>xb\<in>(\<K> - {xa}). (indicat_real {(p, q)} (xa, xb))) / real (card (\<K> - {xa})))" 
    using pmf_return
    by auto

  then have "(\<Sum>xa\<in>\<K>. pmf (?pmf_fun xa) (p, q)) =
    (\<Sum>xa\<in>\<K>. (\<Sum>xb\<in>(\<K> - {xa}). (indicat_real {(p, q)} (xa, xb)))) / (card \<K> - 1)"  
    by (auto simp add: sum_divide_distrib)

  then have "?pmf_whole (p, q) 
  = ((\<Sum>xa\<in>\<K>. (\<Sum>xb\<in>(\<K> - {xa}). (indicat_real {(p, q)} (xa, xb)))) / (card \<K> - 1)) / (card \<K>)" 
    using pmf_bind_1 by auto
  then have right_side_final: "?pmf_whole (p, q) 
  = ((\<Sum>xa\<in>\<K>. (\<Sum>xb\<in>(\<K> - {xa}). (indicat_real {(p, q)} (xa, xb))))) / ((card \<K> - 1) * (card \<K>))"
    by auto

  consider (case_0) "p \<notin> \<K> \<or> q \<notin> \<K> \<or> p = q" | (case_1) "p \<in> \<K> \<and> q \<in> \<K> \<and> p \<noteq> q" by auto
  then show ?thesis
    proof (cases)
      case case_0
      then have not_in: "(p, q) \<notin> \<K> \<times> \<K> - ?id" by auto
      then have "indicat_real (\<K> \<times> \<K> - ?id) (p, q) = 0" by auto
      from left_side_final this
      have left_side_zero: "pmf (pmf_of_set (\<K> \<times> \<K> - ?id)) (p, q) = 0" by auto

      have "\<And>x y. x \<in> \<K> \<Longrightarrow> y \<in> \<K> - {x} \<Longrightarrow> x \<noteq> y" by auto
      then have implies_notin: "\<And>x y. x \<in> \<K> \<Longrightarrow> y \<in> \<K> - {x} \<Longrightarrow> (x, y) \<in> \<K> \<times> \<K> - ?id"
        by auto
      have "\<And>x y. (x, y) \<in> \<K> \<times> \<K> - ?id \<Longrightarrow> (x, y) \<noteq> (p, q)" 
        using not_in by auto
      from this implies_notin have 
        "\<And>x y. x \<in> \<K> \<Longrightarrow> y \<in> \<K> - {x} \<Longrightarrow> (x, y) \<notin> {(p, q)}" by auto
      then have  
        "\<And>x y. x \<in> \<K> \<Longrightarrow> y \<in> \<K> - {x} \<Longrightarrow> indicat_real {(p, q)} (x, y) = 0" 
        by fastforce
      
      from this have "((\<Sum>xa\<in>\<K>. (\<Sum>xb\<in>(\<K> - {xa}). (indicat_real {(p, q)} (xa, xb))))) = 0" by auto
      then have "?pmf_whole (p, q) = 0" using right_side_final by auto
      thus ?thesis using left_side_zero by auto
    next
      case case_1
      then have is_in: "(p, q) \<in> \<K> \<times> \<K> - ?id" 
        by auto
      then have "indicat_real (\<K> \<times> \<K> - ?id) (p, q) = 1" by auto
      from left_side_final this
      have left_side_prob: "pmf (pmf_of_set (\<K> \<times> \<K> - ?id)) (p, q) = 1 / (card \<K> * (card \<K> - 1))" 
        by auto

      from is_in have "\<exists>x y. (x, y) \<in> \<K> \<times> \<K> - ?id \<and> (x, y) = (p, q)" by auto
      then have "\<exists>x y. x \<in> \<K> \<and> y \<in> \<K> - {x} \<and> (x, y) \<in> {(p, q)}" by auto
      then obtain x y where x_y_obtain: "x \<in> \<K>" "y \<in> \<K> - {x}" "(x, y) \<in> {(p, q)}" by blast
      
      then have "x \<in> \<K> \<and> y \<in> \<K> - {x} \<and> (indicat_real {(p, q)} (x, y) = 1)"
        by fastforce

      let ?f_1 = "\<lambda>_. 1"
      let ?f_2 = "\<lambda>xa. card ((\<K> - {xa}) \<inter> {q}) "

      have "\<And>a b. indicat_real {(p, q)} (a, b) = indicat_real {p} a * indicat_real {q} b" 
        by (simp add: indicator_def)
      then have
        "(\<Sum>xa\<in>\<K>. (\<Sum>xb\<in>(\<K> - {xa}). (indicat_real {(p, q)} (xa, xb)))) =
         (\<Sum>xa\<in>\<K>. (\<Sum>xb\<in>(\<K> - {xa}). indicat_real {p} xa * indicat_real {q} xb))" 
        by auto
      then have 
        sum_last: "(\<Sum>xa\<in>\<K>. (\<Sum>xb\<in>(\<K> - {xa}). (indicat_real {(p, q)} (xa, xb)))) =
         (\<Sum>xa\<in>\<K>. indicat_real {p} xa * (\<Sum>xb\<in>(\<K> - {xa}). (?f_1 xb) * indicat_real {q} xb))" 
        by (simp add: sum_distrib_left)
      
      have "\<And>xa. (\<Sum>xb\<in>\<K> - {xa}. (?f_1 xb) * indicat_real {q} xb)
        = sum ?f_1 ((\<K> - {xa}) \<inter> {q})" 
        by (simp add: assms(1) indicator_def)
      from sum_last this have "(\<Sum>xa\<in>\<K>. (\<Sum>xb\<in>(\<K> - {xa}). (indicat_real {(p, q)} (xa, xb)))) =
         (\<Sum>xa\<in>\<K>. indicat_real {p} xa * sum ?f_1 ((\<K> - {xa}) \<inter> {q}))" by auto  
      then have "(\<Sum>xa\<in>\<K>. (\<Sum>xb\<in>(\<K> - {xa}). (indicat_real {(p, q)} (xa, xb)))) =
         (\<Sum>xa\<in>\<K>. indicat_real {p} xa * card ((\<K> - {xa}) \<inter> {q})) " by auto
      
      then have "(\<Sum>xa\<in>\<K>. (\<Sum>xb\<in>(\<K> - {xa}). (indicat_real {(p, q)} (xa, xb)))) =
         (\<Sum>xa\<in>\<K>. indicat_real {p} xa * ?f_2 xa)" by auto
      then have "(\<Sum>xa\<in>\<K>. (\<Sum>xb\<in>(\<K> - {xa}). (indicat_real {(p, q)} (xa, xb)))) =
         sum ?f_2 (\<K> \<inter> {p})" 
        by (auto simp add: assms(1) indicator_def)
      then have "(\<Sum>xa\<in>\<K>. (\<Sum>xb\<in>(\<K> - {xa}). (indicat_real {(p, q)} (xa, xb)))) =
         card ((\<K> - {p}) \<inter> {q})" 
        using case_1 by auto
      then have "(\<Sum>xa\<in>\<K>. (\<Sum>xb\<in>(\<K> - {xa}). (indicat_real {(p, q)} (xa, xb)))) = 1" 
        using case_1 by auto
      from this right_side_final 
      have 
      "((\<Sum>xa\<in>\<K>. (\<Sum>xb\<in>(\<K> - {xa}). (indicat_real {(p, q)} (xa, xb))))) / ((card \<K> - 1) * (card \<K>)) 
      = 1 / ((card \<K> - 1) * (card \<K>))" by auto
      then have "?pmf_whole (p, q) = 1 / ((card \<K> - 1) * (card \<K>))" using right_side_final by auto
      thus ?thesis using left_side_prob by auto
    qed  
qed


(*Problems:
  1. The set is infinite. Hence, spmf_of_set won't work here
    - Idea 1: Limit the set by a random number?
    - Idea 2: Find another way to sample (however, with infinite amount of keys, we cannot find a
    probability distribution with non-zero constant probabilities, which will force us to use a 
    distribution that will prioritize some values more than the others.
    - Idea 3: Since the sampling is not defined in any literature, we may write multiple key 
    generation algorithms and try to prove the desired properties with these algorithms. Then, we 
    prove the correctness/IND-CPA secureness for different sampling techniques which may also be 
    interesting (for instance: with which sampling is it not IND-CPA-secure anymore?)
  2. The probabilities change after we remove an element from the set. We may need to sample the 
  tuple from a finite set of tuples of valid private keys, or maybe show that the probability 
  distribution doesn't change in this case. Does it really change? Or does it matter that it changes?

  Idea: Use the current standard (3000 according to Technical Guidelines for 
  Federal Office for Information Security (BSI)) *)

definition encrypt_prob :: "pub_key \<Rightarrow> bitstring \<Rightarrow> (bitstring list \<times> nat) pmf" where
"encrypt_prob n m = do {
   let \<Z> = {(z::nat). z < n \<and> coprime z n};
   r \<leftarrow> pmf_of_set \<Z>;
   return_pmf (encrypt_alt n m r)
}"


definition decrypt_prob :: "priv_key \<Rightarrow> (bitstring list \<times> nat) \<Rightarrow> bitstring pmf" where
"decrypt_prob = (\<lambda>(p,q) c. return_pmf (decrypt_alt p q c))"


theorem
  assumes 
    "m \<noteq> []"
    "card {(p::nat). prime p \<and>  p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u} > 1" 
  shows  
    "pmf (do {
    (n, (p, q)) \<leftarrow> key_gen_prob l u;
    (c, x) \<leftarrow> (encrypt_prob n m);
    return_pmf (decrypt_alt p q (c, x) = m)}) True = 1"
proof - 
  have "do {
  (n, (p, q)) \<leftarrow> key_gen_prob l u;
  (c, x) \<leftarrow> (encrypt_prob n m);
  return_pmf (decrypt_alt p q (c, x) = m)} = 
  do {
  (n, (p, q)) \<leftarrow> key_gen_prob l u;
  let \<Z> = {(z::nat). z < n \<and> coprime z n};
  r \<leftarrow> pmf_of_set \<Z>;
  (c, x) \<leftarrow>  return_pmf (encrypt_alt n m r);
  return_pmf (decrypt_alt p q (c, x) = m)}" 
    unfolding encrypt_prob_def 
    by (auto simp add: bind_assoc_pmf)

  also have "... =
   do {
  (n, (p, q)) \<leftarrow> key_gen_prob l u;
  let \<Z> = {(z::nat). z < n \<and> coprime z n};
  r \<leftarrow> pmf_of_set \<Z>;
  return_pmf (decrypt_alt p q (encrypt_alt n m r) = m)}" 
    by (auto simp add: bind_return_pmf)

  also have "... = 
   do {
  (n, (p, q)) \<leftarrow> do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
   p \<leftarrow> pmf_of_set \<K>; 
   q \<leftarrow> pmf_of_set (\<K> - {p});
  return_pmf (key_gen p q)
  };
  let \<Z> = {(z::nat). z < n \<and> coprime z n};
  r \<leftarrow> pmf_of_set \<Z>;
  return_pmf (decrypt_alt p q (encrypt_alt n m r) = m)}" 
    unfolding key_gen_prob_def
    by auto

  also have "... = 
   do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> pmf_of_set \<K>; 
  q \<leftarrow> pmf_of_set (\<K> - {p});
  (n, (p, q)) \<leftarrow> return_pmf (key_gen p q);
  let \<Z> = {(z::nat). z < n \<and> coprime z n};
  r \<leftarrow> pmf_of_set \<Z>;
  return_pmf (decrypt_alt p q (encrypt_alt n m r) = m)}" 
    unfolding Let_def 
    by (auto simp add: bind_assoc_pmf)

  also have "... = 
   do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> pmf_of_set \<K>; 
  q \<leftarrow> pmf_of_set (\<K> - {p});
  (n, (p, q)) \<leftarrow> return_pmf ((p * q, (p, q)));
  let \<Z> = {(z::nat). z < n \<and> coprime z n};
  r \<leftarrow> pmf_of_set \<Z>;
  return_pmf (decrypt_alt p q (encrypt_alt n m r) = m)}" 
    unfolding key_gen_def 
    by auto

 also have "... = 
   do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> pmf_of_set \<K>; 
  q \<leftarrow> pmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> pmf_of_set \<Z>;
  return_pmf (decrypt_alt p q (encrypt_alt (p * q) m r) = m)}" 
   by (auto simp add: bind_return_pmf)

  from calculation have "do {
  (n, (p, q)) \<leftarrow> key_gen_prob l u;
  (c, x) \<leftarrow> (encrypt_prob n m);
  return_pmf (decrypt_alt p q (c, x) = m)} 
  = do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> pmf_of_set \<K>; 
  q \<leftarrow> pmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> pmf_of_set \<Z>;
  return_pmf (decrypt_alt p q (encrypt_alt (p * q) m r) = m)}" 
    using key_gen_def
    by (auto simp add: bind_return_pmf)

  then have step_1: "
  pmf (do {
  (n, (p, q)) \<leftarrow> key_gen_prob l u;
  (c, x) \<leftarrow> (encrypt_prob n m);
  return_pmf (decrypt_alt p q (c, x) = m)})
  = 
  pmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> pmf_of_set \<K>; 
  q \<leftarrow> pmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> pmf_of_set \<Z>;
  return_pmf (decrypt_alt p q (encrypt_alt (p * q) m r) = m)})"
    by auto

then have "
  pmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> pmf_of_set \<K>; 
  q \<leftarrow> pmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> pmf_of_set \<Z>;
  return_pmf (decrypt_alt p q (encrypt_alt (p * q) m r) = m)})
  = 
  pmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> pmf_of_set \<K>; 
  q \<leftarrow> pmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> pmf_of_set \<Z>;
  return_pmf ((prime p \<longrightarrow> decrypt_alt p q (encrypt_alt (p * q) m r) = m)\<and> (\<not>prime p \<longrightarrow> decrypt_alt p q (encrypt_alt (p * q) m r) = m))})"
  by auto

  
  have correctness_int: "(prime p \<and> prime q \<and> p mod 4 = 3 \<and> q mod 4 = 3 \<and> r < p * q \<and> coprime r (p * q) \<and> p \<noteq> q \<and> m \<noteq> []) \<longrightarrow> decrypt_alt p q (encrypt_alt (p * q) m r) = m"
  using correctness
  by auto

  have "A = ((B \<longrightarrow> A) \<and> (\<not>B \<longrightarrow> A))" 
    by auto

  then have iff_rule: "(decrypt_alt p q (encrypt_alt (p * q) m r) = m) = 
        (((prime p \<and> prime q \<and> p mod 4 = 3 \<and> q mod 4 = 3 \<and> r < p * q \<and> coprime r (p * q) \<and> p \<noteq> q \<and> m \<noteq> []) \<longrightarrow> decrypt_alt p q (encrypt_alt (p * q) m r) = m)
      \<and> (\<not>(prime p \<and> prime q \<and> p mod 4 = 3 \<and> q mod 4 = 3 \<and> r < p * q \<and> coprime r (p * q) \<and> p \<noteq> q \<and> m \<noteq> []) \<longrightarrow> decrypt_alt p q (encrypt_alt (p * q) m r) = m))
        " 
    by auto
 
  let ?\<K> = "{(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u}"
  let ?\<Z> = "{(z::nat). z < p * q \<and> coprime z (p * q)}"

  have \<K>_finite: "finite ?\<K>" 
    by auto
  have \<K>_not_empty: "?\<K> \<noteq> {}"
    using assms(2)
    by fastforce
  from \<K>_finite \<K>_not_empty have \<K>_finite': "finite' ?\<K>" 
    by auto
  
  have \<K>_not_empty_after_p: "\<And>p. ?\<K> - {p} \<noteq> {}"
    using assms(2) 
    by (metis (no_types, lifting) \<K>_finite' card_Diff_singleton_if card_gt_0_iff zero_less_diff)
  then have \<K>_card_after_p: "card ?\<K> - 1 > 0" 
    using assms(2) by linarith
  from this \<K>_finite have \<K>_finite_after_p: "\<And>p. finite (?\<K> - {p})" 
    by auto


  then have "
  pmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> pmf_of_set \<K>; 
  q \<leftarrow> pmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> pmf_of_set \<Z>;
  return_pmf (decrypt_alt p q (encrypt_alt (p * q) m r) = m)}) True
  = 
  pmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> pmf_of_set \<K>; 
  q \<leftarrow> pmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> pmf_of_set \<Z>;
  return_pmf ((((prime p \<and> prime q \<and> p mod 4 = 3 \<and> q mod 4 = 3 \<and> r < p * q \<and> coprime r (p * q) \<and> p \<noteq> q \<and> m \<noteq> []) \<longrightarrow> decrypt_alt p q (encrypt_alt (p * q) m r) = m)
      \<and> (\<not>(prime p \<and> prime q \<and> p mod 4 = 3 \<and> q mod 4 = 3 \<and> r < p * q \<and> coprime r (p * q) \<and> p \<noteq> q \<and> m \<noteq> []) \<longrightarrow> decrypt_alt p q (encrypt_alt (p * q) m r) = m)))}) 
  True"
    using iff_rule[symmetric]
    by metis
  then have "
  pmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> pmf_of_set \<K>; 
  q \<leftarrow> pmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> pmf_of_set \<Z>;
  return_pmf (decrypt_alt p q (encrypt_alt (p * q) m r) = m)}) True
  = 
  pmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> pmf_of_set \<K>; 
  q \<leftarrow> pmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> pmf_of_set \<Z>;
  return_pmf ((\<not>(prime p \<and> prime q \<and> p mod 4 = 3 \<and> q mod 4 = 3 \<and> r < p * q \<and> coprime r (p * q) \<and> p \<noteq> q \<and> m \<noteq> []) \<longrightarrow> decrypt_alt p q (encrypt_alt (p * q) m r) = m))}) 
  True"
    using correctness  
    by algebra

  then have "
  pmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> pmf_of_set \<K>; 
  q \<leftarrow> pmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> pmf_of_set \<Z>;
  return_pmf (decrypt_alt p q (encrypt_alt (p * q) m r) = m)}) True
  = 
  pmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> pmf_of_set \<K>; 
  q \<leftarrow> pmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> pmf_of_set \<Z>;
  return_pmf ((prime p \<and> prime q \<and> p mod 4 = 3 \<and> q mod 4 = 3 \<and> r < p * q \<and> coprime r (p * q) \<and> p \<noteq> q \<and> m \<noteq> []) \<or> decrypt_alt p q (encrypt_alt (p * q) m r) = m)}) 
  True" 
    by linarith
  then have "
  pmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> pmf_of_set \<K>; 
  q \<leftarrow> pmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> pmf_of_set \<Z>;
  return_pmf (decrypt_alt p q (encrypt_alt (p * q) m r) = m)}) True
  = 
  pmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> pmf_of_set \<K>; 
  q \<leftarrow> pmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> pmf_of_set \<Z>;
  return_pmf ((prime p \<and> prime q \<and> p mod 4 = 3 \<and> q mod 4 = 3 \<and> r < p * q \<and> coprime r (p * q) \<and> p \<noteq> q) \<or> decrypt_alt p q (encrypt_alt (p * q) m r) = m)}) 
  True" 
    using assms(1) by auto

  then have  "
  pmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> pmf_of_set \<K>; 
  q \<leftarrow> pmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> pmf_of_set \<Z>;
  return_pmf (decrypt_alt p q (encrypt_alt (p * q) m r) = m)}) True
  = 
  pmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> pmf_of_set \<K>; 
  q \<leftarrow> pmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> pmf_of_set \<Z>;
  return_pmf ((((p \<in> \<K> \<and> q \<in> \<K> - {p} \<and> r \<in> \<Z>) \<longrightarrow> prime p \<and> prime q \<and> p mod 4 = 3 \<and> q mod 4 = 3 \<and> r < p * q \<and> coprime r (p * q) \<and> p \<noteq> q)
 \<and> (\<not>(p \<in> \<K> \<and> q \<in> \<K> - {p} \<and> r \<in> \<Z>) \<longrightarrow> prime p \<and> prime q \<and> p mod 4 = 3 \<and> q mod 4 = 3 \<and> r < p * q \<and> coprime r (p * q) \<and> p \<noteq> q))
 \<or> decrypt_alt p q (encrypt_alt (p * q) m r) = m)})
  True" 
    by metis

  then have  "
  pmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> pmf_of_set \<K>; 
  q \<leftarrow> pmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> pmf_of_set \<Z>;
  return_pmf (decrypt_alt p q (encrypt_alt (p * q) m r) = m)}) True
  = 
  pmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> pmf_of_set \<K>; 
  q \<leftarrow> pmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> pmf_of_set \<Z>;
  return_pmf (((\<not>(p \<in> \<K> \<and> q \<in> \<K> - {p} \<and> r \<in> \<Z>) \<longrightarrow> prime p \<and> prime q \<and> p mod 4 = 3 \<and> q mod 4 = 3 \<and> r < p * q \<and> coprime r (p * q) \<and> p \<noteq> q))
 \<or> decrypt_alt p q (encrypt_alt (p * q) m r) = m)})
  True" 
    by simp

  then have spmf_last:  "
  pmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> pmf_of_set \<K>; 
  q \<leftarrow> pmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> pmf_of_set \<Z>;
  return_pmf (decrypt_alt p q (encrypt_alt (p * q) m r) = m)}) True
  = 
  pmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> pmf_of_set \<K>; 
  q \<leftarrow> pmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> pmf_of_set \<Z>;
  return_pmf (((p \<in> \<K> \<and> q \<in> \<K> - {p} \<and> r \<in> \<Z>) \<or> (prime p \<and> prime q \<and> p mod 4 = 3 \<and> q mod 4 = 3 \<and> r < p * q \<and> coprime r (p * q) \<and> p \<noteq> q))
 \<or> decrypt_alt p q (encrypt_alt (p * q) m r) = m)})
  True" 
    by linarith

  let ?pmf = "(do {
  p \<leftarrow> pmf_of_set ?\<K>; 
  q \<leftarrow> pmf_of_set (?\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> pmf_of_set \<Z>;
  return_pmf (((p \<in> ?\<K> \<and> q \<in> ?\<K> - {p} \<and> r \<in> \<Z>) \<or> (prime p \<and> prime q \<and> p mod 4 = 3 \<and> q mod 4 = 3 \<and> r < p * q \<and> coprime r (p * q) \<and> p \<noteq> q))
 \<or> decrypt_alt p q (encrypt_alt (p * q) m r) = m)})"

  have replace_pmf: "pmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> pmf_of_set \<K>; 
  q \<leftarrow> pmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> pmf_of_set \<Z>;
  return_pmf (((p \<in> \<K> \<and> q \<in> \<K> - {p} \<and> r \<in> \<Z>) \<or> (prime p \<and> prime q \<and> p mod 4 = 3 \<and> q mod 4 = 3 \<and> r < p * q \<and> coprime r (p * q) \<and> p \<noteq> q))
 \<or> decrypt_alt p q (encrypt_alt (p * q) m r) = m)})
  True = pmf ?pmf True" 
  by metis
 
  
  let ?pmf_fun = "(\<lambda>p. pmf_of_set (?\<K> - {p}) \<bind>
                  (\<lambda>q. let \<Z> = {z. z < p * q \<and> coprime z (p * q)}
                      in pmf_of_set \<Z> \<bind>
                         (\<lambda>r. return_pmf
                               ((p \<in> ?\<K> \<and> q \<in> ?\<K> - {p} \<and> r \<in> \<Z> \<or>
                                 prime p \<and>
                                 prime q \<and>
                                 p mod 4 = 3 \<and> q mod 4 = 3 \<and> r < p * q \<and> coprime r (p * q) \<and> p \<noteq> q) \<or>
                                decrypt_alt p q (encrypt_alt (p * q) m r) = m))))"

  let ?pmf_fun' = "(\<lambda>p. pmf_of_set (?\<K> - {p}) \<bind>
                  (\<lambda>q. let \<Z> = {z. z < p * q \<and> coprime z (p * q)}
                      in pmf_of_set \<Z> \<bind>
                         (\<lambda>r. return_pmf
                               ((q \<in> ?\<K> - {p} \<and> r \<in> \<Z> \<or>
                                 prime q \<and>
                                q mod 4 = 3 \<and> r < p * q \<and> coprime r (p * q) \<and> p \<noteq> q) \<or>
                                decrypt_alt p q (encrypt_alt (p * q) m r) = m))))"
  
  have step_3: "pmf ?pmf True = (\<Sum>xa\<in>?\<K>. pmf (?pmf_fun xa) True) / real (card ?\<K>)"
    using pmf_bind_pmf_of_set \<K>_finite \<K>_not_empty
    by (simp add: pmf_bind_pmf_of_set)
  then have "pmf ?pmf True = (\<Sum>xa\<in>?\<K>. pmf (?pmf_fun' xa) True) / real (card ?\<K>)"
    by auto

  let ?pmf_fun'' = "\<lambda>xa. (\<lambda>q. let \<Z> = {z. z < xa * q \<and> coprime z (xa * q)}
                      in pmf_of_set \<Z> \<bind>
                         (\<lambda>r. return_pmf
                               ((q \<in> ?\<K> - {xa} \<and> r \<in> \<Z> \<or>
                                 prime q \<and>
                                 q mod 4 = 3 \<and> r < xa * q \<and> coprime r (xa * q) \<and> xa \<noteq> q) \<or>
                                decrypt_alt xa q (encrypt_alt (xa * q) m r) = m)))"

  have "\<And>xa. (pmf (?pmf_fun' xa) True) = 
     (\<Sum>xb\<in>(?\<K> - {xa}). pmf ((?pmf_fun'' xa) xb) True) / real (card (?\<K> - {xa}))"
  using \<K>_finite_after_p \<K>_not_empty_after_p
  by (auto simp add: pmf_bind_pmf_of_set)

  then have "(\<Sum>xa\<in>?\<K>. pmf (?pmf_fun' xa) True) = 
     (\<Sum>xa\<in>?\<K>. (\<Sum>xb\<in>(?\<K> - {xa}). pmf ((?pmf_fun'' xa) xb) True) / real (card (?\<K> - {xa})))" 
    by auto

  then have "(\<Sum>xa\<in>?\<K>. pmf (?pmf_fun' xa) True) =
    (\<Sum>xa\<in>?\<K>. (\<Sum>xb\<in>(?\<K> - {xa}). pmf ((?pmf_fun'' xa) xb) True)) / real (card ?\<K> - 1)" 
   by (simp add: sum_divide_distrib)  

  then have q_escaped: "(\<Sum>xa\<in>?\<K>. pmf (?pmf_fun' xa) True) / real (card ?\<K>) = 
     (\<Sum>xa\<in>?\<K>. (\<Sum>xb\<in>(?\<K> - {xa}). pmf ((?pmf_fun'' xa) xb) True)) / (real (card ?\<K> - 1) * real (card ?\<K>))"
  by auto

  let ?pmf_fun''' = "\<lambda>xa. \<lambda>q. (let \<Z> = {z. z < xa * q \<and> coprime z (xa * q)}
                      in pmf_of_set \<Z> \<bind>
                         (\<lambda>r. return_pmf
                               ((r \<in> \<Z> \<or>
                                 r < xa * q \<and> coprime r (xa * q) \<and> xa \<noteq> q) \<or>
                               decrypt_alt xa q (encrypt_alt (xa * q) m r) = m)))"
  
  let ?\<Z> = "\<lambda>xa xb. {(z::nat). z < xa * xb \<and> coprime z (xa * xb)}"

  let ?pmf_fun_3alt = "\<lambda>xa. \<lambda>q. (pmf_of_set (?\<Z> xa q) \<bind>
                         (\<lambda>r. return_pmf
                               ((r \<in> (?\<Z> xa q) \<or>
                                 r < xa * q \<and> coprime r (xa * q) \<and> xa \<noteq> q) \<or>
                               decrypt_alt xa q (encrypt_alt (xa * q) m r) = m)))"
  
  let ?pmf_fun_4 = "\<lambda>xa xb. 
                          (\<lambda>r. (return_pmf
                            ((r \<in> (?\<Z> xa xb) \<or>
                             r < xa * xb \<and> coprime r (xa * xb) \<and> xa \<noteq> xb) \<or>
                         decrypt_alt xa xb (encrypt_alt (xa * xb) m r) = m)))"

  from q_escaped have ff: "(\<Sum>xa\<in>?\<K>. pmf (?pmf_fun' xa) True) / real (card ?\<K>) = 
     (\<Sum>xa\<in>?\<K>. (\<Sum>xb\<in>(?\<K> - {xa}). pmf ((?pmf_fun''' xa) xb) True)) / (real (card ?\<K> - 1) * real (card ?\<K>))"
    by auto

  have "\<And>p q. (p \<in> ?\<K> \<and> q \<in> ?\<K>) \<longrightarrow> 2 \<le> p \<and> 2 \<le> q" 
    by auto
  then have "\<And>p q. (p \<in> ?\<K> \<and> q \<in> ?\<K>) \<longrightarrow> 1 < p * q" 
   using One_nat_def mem_Collect_eq one_less_mult prime_gt_1_nat
   by (metis (mono_tags, lifting))
  then have "\<And>p q. (p \<in> ?\<K> \<and> q \<in> ?\<K>) \<longrightarrow> 1 < p * q \<and> coprime 1 (p * q)" 
    by auto
  then have "\<And>p q. (p \<in> ?\<K> \<and> q \<in> ?\<K>) \<longrightarrow> 1 \<in> ?\<Z> p q"  
    by blast
  then have \<Z>_not_empty: "\<And>p q. (p \<in> ?\<K> \<and> q \<in> ?\<K>) \<Longrightarrow> ?\<Z> p q \<noteq> {}" 
    by blast

  have \<Z>_finite: "\<And>p q. finite (?\<Z> p q)" 
    by auto 

  have "\<And>xa xb xc. xc \<in> (?\<Z> xa xb)
     \<Longrightarrow> pmf ((?pmf_fun_4 xa xb) xc) True = 1" by auto 
  
  have "\<And>xa xb. xa \<in> ?\<K> \<Longrightarrow> xb \<in> ?\<K> - {xa} \<Longrightarrow> pmf (?pmf_fun_3alt xa xb) True = 
    (\<Sum>xc\<in>(?\<Z> xa xb). pmf ((?pmf_fun_4 xa xb) xc) True) / real (card (?\<Z> xa xb))" 
    using \<Z>_finite \<Z>_not_empty
    by (simp add: pmf_bind_pmf_of_set)
  then have "\<And>xa xb. xa \<in> ?\<K> \<Longrightarrow> xb \<in> ?\<K> - {xa} \<Longrightarrow> pmf (?pmf_fun_3alt xa xb) True = 
    (\<Sum>xc\<in>(?\<Z> xa xb). 1) / real (card (?\<Z> xa xb))" 
    by auto
  then have "\<And>xa xb. xa \<in> ?\<K> \<Longrightarrow> xb \<in> ?\<K> - {xa} \<Longrightarrow> pmf (?pmf_fun_3alt xa xb) True = 
    (card (?\<Z> xa xb)) / (card (?\<Z> xa xb))" 
    by auto
  then have "\<And>xa xb. xa \<in> ?\<K> \<Longrightarrow> xb \<in> ?\<K> - {xa} \<Longrightarrow> pmf (?pmf_fun_3alt xa xb) True = 1" 
    using \<Z>_not_empty
    by auto

  from ff this have 
    "(\<Sum>xa\<in>?\<K>. pmf (?pmf_fun' xa) True) / real (card ?\<K>) = 
     (\<Sum>xa\<in>?\<K>. (\<Sum>xb\<in>(?\<K> - {xa}). 1)) / (real (card ?\<K> - 1) * real (card ?\<K>))"
    by auto
  then have  
    "(\<Sum>xa\<in>?\<K>. pmf (?pmf_fun' xa) True) / real (card ?\<K>) = 
     (\<Sum>xa\<in>?\<K>. (card ?\<K> - 1)) / (real (card ?\<K> - 1) * real (card ?\<K>))"
    by auto
  then have
    "(\<Sum>xa\<in>?\<K>. pmf (?pmf_fun' xa) True) / real (card ?\<K>) = 
    ((card ?\<K>) * (card ?\<K> - 1)) / ((card ?\<K> - 1) * (card ?\<K>))"
    by auto
  then have step_4: "(\<Sum>xa\<in>?\<K>. pmf (?pmf_fun' xa) True) / real (card ?\<K>) = 1"
    using \<K>_not_empty \<K>_card_after_p div_self
    by auto

  from step_1 spmf_last
  have "pmf (do {
  (n, (p, q)) \<leftarrow> key_gen_prob l u;
  (c, x) \<leftarrow> (encrypt_prob n m);
  return_pmf (decrypt_alt p q (c, x) = m)}) True
  = pmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> pmf_of_set \<K>; 
  q \<leftarrow> pmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> pmf_of_set \<Z>;
  return_pmf (((p \<in> \<K> \<and> q \<in> \<K> - {p} \<and> r \<in> \<Z>) \<or> (prime p \<and> prime q \<and> p mod 4 = 3 \<and> q mod 4 = 3 \<and> r < p * q \<and> coprime r (p * q) \<and> p \<noteq> q))
 \<or> decrypt_alt p q (encrypt_alt (p * q) m r) = m)})
  True" 
    by auto

  then have "pmf (do {
  (n, (p, q)) \<leftarrow> key_gen_prob l u;
  (c, x) \<leftarrow> (encrypt_prob n m);
  return_pmf (decrypt_alt p q (c, x) = m)}) True = 
  (\<Sum>xa\<in>?\<K>. pmf (?pmf_fun xa) True) / real (card ?\<K>)"
   using step_3 replace_pmf
   by presburger

  then show ?thesis 
    using step_4
    by auto
qed



end