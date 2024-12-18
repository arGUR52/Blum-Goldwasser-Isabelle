theory BG_prob imports
  Main
  BG_aux
  BG_formalization
  BG_correctness
  "Crypto_Standards.Words"
  "CryptHOL.CryptHOL"
  "ABY3_Protocols.Spmf_Common"
begin

section "Formalization of Blum-Goldwasser cryptosystem in a probabilistic setting"

type_synonym pub_key = nat
type_synonym priv_key = "nat \<times> nat"

subsection "Key generation"

text "We generate a key by uniformally sampling a set of natural numbers that are congruent to 3 
modulo 4. To ensure that \<open>p \<noteq> q\<close>, we remove the first selected number from the sample set."
definition key_gen_prob :: "nat \<Rightarrow> nat \<Rightarrow> (pub_key \<times> priv_key) spmf"
where 
  "key_gen_prob lower upper = do {
    let \<K> = {(p::nat). prime p \<and>  p mod 4 = 3 \<and> lower \<le> p \<and> p \<le> upper};
    p \<leftarrow> spmf_of_set \<K>; 
    q \<leftarrow> spmf_of_set (\<K> - {p});
    return_spmf (key_gen p q)
  }"

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

definition encrypt_prob :: "pub_key \<Rightarrow> bitstring \<Rightarrow> (bitstring list \<times> nat) spmf" where
"encrypt_prob n m = do {
   let \<Z> = {(z::nat). z < n \<and> coprime z n};
   r \<leftarrow> spmf_of_set \<Z>;
   return_spmf (encrypt_alt n m r)
}"

definition decrypt_prob :: "priv_key \<Rightarrow> (bitstring list \<times> nat) \<Rightarrow> bitstring spmf" where
"decrypt_prob = (\<lambda>(p,q) c. return_spmf (decrypt_alt p q c))"

theorem
  assumes "m \<noteq> []"
  shows  "spmf (do {
  (n, (p, q)) \<leftarrow> key_gen_prob l u;
  (c, x) \<leftarrow> (encrypt_prob n m);
  return_spmf (decrypt_alt p q (c, x) = m)}) True = 1"
proof - 
  have "do {
  (n, (p, q)) \<leftarrow> key_gen_prob l u;
  (c, x) \<leftarrow> (encrypt_prob n m);
  return_spmf (decrypt_alt p q (c, x) = m)} = 
  do {
  (n, (p, q)) \<leftarrow> key_gen_prob l u;
  let \<Z> = {(z::nat). z < n \<and> coprime z n};
  r \<leftarrow> spmf_of_set \<Z>;
  (c, x) \<leftarrow>  return_spmf (encrypt_alt n m r);
  return_spmf (decrypt_alt p q (c, x) = m)}" 
    unfolding encrypt_prob_def 
    by auto
  also have "... = 
   do {
  (n, (p, q)) \<leftarrow> key_gen_prob l u;
  let \<Z> = {(z::nat). z < n \<and> coprime z n};
  r \<leftarrow> spmf_of_set \<Z>;
  return_spmf (decrypt_alt p q (encrypt_alt n m r) = m)}" 
    by auto
  also have "... = 
   do {
  (n, (p, q)) \<leftarrow> do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
   p \<leftarrow> spmf_of_set \<K>; 
   q \<leftarrow> spmf_of_set (\<K> - {p});
  return_spmf (key_gen p q)
  };
  let \<Z> = {(z::nat). z < n \<and> coprime z n};
  r \<leftarrow> spmf_of_set \<Z>;
  return_spmf (decrypt_alt p q (encrypt_alt n m r) = m)}" 
    unfolding key_gen_prob_def
    by auto
  also have "... = 
   do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> spmf_of_set \<K>; 
  q \<leftarrow> spmf_of_set (\<K> - {p});
  (n, (p, q)) \<leftarrow> return_spmf (key_gen p q);
  let \<Z> = {(z::nat). z < n \<and> coprime z n};
  r \<leftarrow> spmf_of_set \<Z>;
  return_spmf (decrypt_alt p q (encrypt_alt n m r) = m)}" 
    unfolding Let_def by auto 
  also have "... = 
   do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> spmf_of_set \<K>; 
  q \<leftarrow> spmf_of_set (\<K> - {p});
  (n, (p, q)) \<leftarrow> return_spmf ((p * q, (p, q)));
  let \<Z> = {(z::nat). z < n \<and> coprime z n};
  r \<leftarrow> spmf_of_set \<Z>;
  return_spmf (decrypt_alt p q (encrypt_alt n m r) = m)}" 
    unfolding key_gen_def by auto
 also have "... = 
   do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> spmf_of_set \<K>; 
  q \<leftarrow> spmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> spmf_of_set \<Z>;
  return_spmf (decrypt_alt p q (encrypt_alt (p * q) m r) = m)}" 
   by auto

  from calculation have "do {
  (n, (p, q)) \<leftarrow> key_gen_prob l u;
  (c, x) \<leftarrow> (encrypt_prob n m);
  return_spmf (decrypt_alt p q (c, x) = m)} 
  = do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> spmf_of_set \<K>; 
  q \<leftarrow> spmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> spmf_of_set \<Z>;
  return_spmf (decrypt_alt p q (encrypt_alt (p * q) m r) = m)}" by auto

  then have "
  spmf (do {
  (n, (p, q)) \<leftarrow> key_gen_prob l u;
  (c, x) \<leftarrow> (encrypt_prob n m);
  return_spmf (decrypt_alt p q (c, x) = m)})
  = 
  spmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> spmf_of_set \<K>; 
  q \<leftarrow> spmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> spmf_of_set \<Z>;
  return_spmf (decrypt_alt p q (encrypt_alt (p * q) m r) = m)})"
    by auto

then have "
  spmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> spmf_of_set \<K>; 
  q \<leftarrow> spmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> spmf_of_set \<Z>;
  return_spmf (decrypt_alt p q (encrypt_alt (p * q) m r) = m)})
  = 
  spmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> spmf_of_set \<K>; 
  q \<leftarrow> spmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> spmf_of_set \<Z>;
  return_spmf ((prime p \<longrightarrow> decrypt_alt p q (encrypt_alt (p * q) m r) = m)\<and> (\<not>prime p \<longrightarrow> decrypt_alt p q (encrypt_alt (p * q) m r) = m))})"
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



  have demorgan: "\<not>(prime p \<and> prime q \<and> p mod 4 = 3 \<and> q mod 4 = 3 \<and> r < p * q \<and> coprime r (p * q) \<and> p \<noteq> q \<and> m \<noteq> []) 
  = (\<not>prime p \<or> \<not>prime q \<or> p mod 4 \<noteq> 3 \<or> q mod 4 \<noteq> 3 \<or> r \<ge> p * q \<or> \<not>coprime r (p * q) \<or> p = q \<or> m = [])" 
    by auto

  then have demorgan_imply: "(\<not>(prime p \<and> prime q \<and> p mod 4 = 3 \<and> q mod 4 = 3 \<and> r < p * q \<and> coprime r (p * q) \<and> p \<noteq> q \<and> m \<noteq> []) \<longrightarrow> decrypt_alt p q (encrypt_alt (p * q) m r) = m) 
  = ((\<not>prime p \<or> \<not>prime q \<or> p mod 4 \<noteq> 3 \<or> q mod 4 \<noteq> 3 \<or> r \<ge> p * q \<or> \<not>coprime r (p * q) \<or> p = q \<or> m = []) \<longrightarrow> decrypt_alt p q (encrypt_alt (p * q) m r) = m)" 
    by auto 

  then have "
  spmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> spmf_of_set \<K>; 
  q \<leftarrow> spmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> spmf_of_set \<Z>;
  return_spmf (decrypt_alt p q (encrypt_alt (p * q) m r) = m)}) True
  = 
  spmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> spmf_of_set \<K>; 
  q \<leftarrow> spmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> spmf_of_set \<Z>;
  return_spmf ((((prime p \<and> prime q \<and> p mod 4 = 3 \<and> q mod 4 = 3 \<and> r < p * q \<and> coprime r (p * q) \<and> p \<noteq> q \<and> m \<noteq> []) \<longrightarrow> decrypt_alt p q (encrypt_alt (p * q) m r) = m)
      \<and> (\<not>(prime p \<and> prime q \<and> p mod 4 = 3 \<and> q mod 4 = 3 \<and> r < p * q \<and> coprime r (p * q) \<and> p \<noteq> q \<and> m \<noteq> []) \<longrightarrow> decrypt_alt p q (encrypt_alt (p * q) m r) = m)))}) 
  True"
    using iff_rule[symmetric]
    by metis
  then have "
  ...
  = 
  spmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> spmf_of_set \<K>; 
  q \<leftarrow> spmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> spmf_of_set \<Z>;
  return_spmf ((\<not>(prime p \<and> prime q \<and> p mod 4 = 3 \<and> q mod 4 = 3 \<and> r < p * q \<and> coprime r (p * q) \<and> p \<noteq> q \<and> m \<noteq> []) \<longrightarrow> decrypt_alt p q (encrypt_alt (p * q) m r) = m))}) 
  True"
    using correctness  
    by algebra

  then have "
  ...
  = 
  spmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> spmf_of_set \<K>; 
  q \<leftarrow> spmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> spmf_of_set \<Z>;
  return_spmf ((prime p \<and> prime q \<and> p mod 4 = 3 \<and> q mod 4 = 3 \<and> r < p * q \<and> coprime r (p * q) \<and> p \<noteq> q \<and> m \<noteq> []) \<or> decrypt_alt p q (encrypt_alt (p * q) m r) = m)}) 
  True" 
    by linarith
  then have "
  ...
  = 
  spmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> spmf_of_set \<K>; 
  q \<leftarrow> spmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> spmf_of_set \<Z>;
  return_spmf ((prime p \<and> prime q \<and> p mod 4 = 3 \<and> q mod 4 = 3 \<and> r < p * q \<and> coprime r (p * q) \<and> p \<noteq> q) \<or> decrypt_alt p q (encrypt_alt (p * q) m r) = m)}) 
  True" 
    using assms by auto

  then have  "
  ...
  = 
  spmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> spmf_of_set \<K>; 
  q \<leftarrow> spmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> spmf_of_set \<Z>;
  return_spmf ((((p \<in> \<K> \<and> q \<in> \<K> - {p} \<and> r \<in> \<Z>) \<longrightarrow> prime p \<and> prime q \<and> p mod 4 = 3 \<and> q mod 4 = 3 \<and> r < p * q \<and> coprime r (p * q) \<and> p \<noteq> q)
 \<and> (\<not>(p \<in> \<K> \<and> q \<in> \<K> - {p} \<and> r \<in> \<Z>) \<longrightarrow> prime p \<and> prime q \<and> p mod 4 = 3 \<and> q mod 4 = 3 \<and> r < p * q \<and> coprime r (p * q) \<and> p \<noteq> q))
 \<or> decrypt_alt p q (encrypt_alt (p * q) m r) = m)})
  True" 
    by metis

  then have  "
  ...
  = 
  spmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> spmf_of_set \<K>; 
  q \<leftarrow> spmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> spmf_of_set \<Z>;
  return_spmf (((\<not>(p \<in> \<K> \<and> q \<in> \<K> - {p} \<and> r \<in> \<Z>) \<longrightarrow> prime p \<and> prime q \<and> p mod 4 = 3 \<and> q mod 4 = 3 \<and> r < p * q \<and> coprime r (p * q) \<and> p \<noteq> q))
 \<or> decrypt_alt p q (encrypt_alt (p * q) m r) = m)})
  True" 
    by simp

  then have spmf_last:  "
  ...
  = 
  spmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> spmf_of_set \<K>; 
  q \<leftarrow> spmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> spmf_of_set \<Z>;
  return_spmf ((((p \<in> \<K> \<and> q \<in> \<K> - {p} \<and> r \<in> \<Z>) \<or> (prime p \<and> prime q \<and> p mod 4 = 3 \<and> q mod 4 = 3 \<and> r < p * q \<and> coprime r (p * q) \<and> p \<noteq> q)))
 \<or> decrypt_alt p q (encrypt_alt (p * q) m r) = m)})
  True" 
    by linarith

  (*Sorry for the mess from here on: i'm trying my best!!!*)
  have "A \<longrightarrow> A \<or> B"
    by auto
  then have "spmf (return_spmf (A \<longrightarrow> A \<or> B)) True = 1" 
    by auto
  then have "spmf (return_spmf (A \<longrightarrow> A \<or> B)) True = 1"


  then have " 
  spmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> spmf_of_set \<K>; 
  q \<leftarrow> spmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> spmf_of_set \<Z>;
  return_spmf (p \<in> \<K> \<and> q \<in> \<K> - {p} \<and> r \<in> \<Z>)})
  True = 1 \<Longrightarrow> 
  spmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> spmf_of_set \<K>; 
  q \<leftarrow> spmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> spmf_of_set \<Z>;
  return_spmf ((((p \<in> \<K> \<and> q \<in> \<K> - {p} \<and> r \<in> \<Z>) \<or> (prime p \<and> prime q \<and> p mod 4 = 3 \<and> q mod 4 = 3 \<and> r < p * q \<and> coprime r (p * q) \<and> p \<noteq> q)))
 \<or> decrypt_alt p q (encrypt_alt (p * q) m r) = m)})
  True = 1" 
  by sorry
  


  

  have "decrypt_alt p q (encrypt_alt (p * q) m r) = m = 
  ((prime p \<longrightarrow> decrypt_alt p q (encrypt_alt (p * q) m r) = m)\<and> (\<not>prime p \<longrightarrow> decrypt_alt p q (encrypt_alt (p * q) m r) = m))"
  by auto




  have "(decrypt_alt p q (encrypt_alt (p * q) m r) = m) \<Longrightarrow> 
  (prime p \<longrightarrow> (decrypt_alt p q (encrypt_alt (p * q) m r) = m))"
    by auto

  let ?\<K> = "{(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u}"

  let ?p = "spmf_of_set ?\<K>"
  let ?q = "?p \<bind> (\<lambda>p. spmf_of_set (?\<K> - {p}))"
  let ?\<Z> = "{(z::nat). z < p * q \<and> coprime z (p * q)}"
  let ?Z = "\<lambda>p q. "

  have "
  spmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> spmf_of_set \<K>; 
  q \<leftarrow> spmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> spmf_of_set \<Z>;
  return_spmf (decrypt_alt p q (encrypt_alt (p * q) m r) = m)}) True =
  spmf (do {
  p \<leftarrow> spmf_of_set ?\<K>; 
  q \<leftarrow> spmf_of_set (?\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> spmf_of_set \<Z>;
  return_spmf (decrypt_alt p q (encrypt_alt (p * q) m r) = m)}) True  
  "
    unfolding Let_def
    by auto
  then have "
  spmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> spmf_of_set \<K>; 
  q \<leftarrow> spmf_of_set (\<K> - {p});
  let \<Z> = {(z::nat). z < p * q \<and> coprime z (p * q)};
  r \<leftarrow> spmf_of_set \<Z>;
  return_spmf (decrypt_alt p q (encrypt_alt (p * q) m r) = m)}) True = 
  spmf (spmf_of_set ?\<K> \<bind> (
  \<lambda>p. (spmf_of_set (?\<K> - {p}) \<bind> (
  \<lambda>q. (spmf_of_set {(z::nat). z < p * q \<and> coprime z (p * q)}) \<bind> (
  \<lambda>r. (return_spmf (decrypt_alt p q (encrypt_alt (p * q) m r) = m))))))) True
  "
    by auto
  then have "
  spmf (spmf_of_set ?\<K> \<bind> (
  \<lambda>p. (spmf_of_set (?\<K> - {p}) \<bind> (
  \<lambda>q. (spmf_of_set {(z::nat). z < p * q \<and> coprime z (p * q)}) \<bind> (
  \<lambda>r. (return_spmf (decrypt_alt p q (encrypt_alt (p * q) m r) = m))))))) True =
  spmf (
  \<lambda>p. (spmf_of_set (?\<K> - {p}) \<bind> (
  \<lambda>q. (spmf_of_set {(z::nat). z < p * q \<and> coprime z (p * q)}) \<bind> (
  \<lambda>r. (return_spmf (decrypt_alt p q (encrypt_alt (p * q) m r) = m)))))) True"
    using spmf_of_set_def bind_def
    by 



  have spmf: "spmf (do {p \<leftarrow> spmf_of_set ?\<K>; return_spmf p}) x = indicator ?\<K> x / card ?\<K>" 
    using spmf_of_set by auto
  have "(x \<notin> ?\<K>) = ((indicator ?\<K> x) = 0)" by auto
  then have "(x \<notin> ?\<K>) = (spmf (do {p \<leftarrow> spmf_of_set ?\<K>; return_spmf p}) x = 0)" 
    using spmf by auto
  then have x_in_k_iff: "(x \<in> ?\<K>) = (spmf (do {p \<leftarrow> spmf_of_set ?\<K>; return_spmf p}) x > 0)" 
    unfolding indicator_def by force
  then have "(spmf (do {p \<leftarrow> spmf_of_set ?\<K>; return_spmf p}) x > 0) \<Longrightarrow> prime x" by auto

  then have "\<not>prime p \<Longrightarrow> spmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> spmf_of_set \<K>; 
  return_spmf p}) p = 0" 
    by (simp add: spmf_of_set)
  have "prime p \<Longrightarrow> spmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> spmf_of_set \<K>; 
  return_spmf p}) p \<ge> 0" 
    using x_in_k_iff
    by auto

  have "\<not>prime p \<Longrightarrow> spmf (cond_spmf (do {
  let \<K> = {(p::nat). prime p \<and> p mod 4 = 3 \<and> l \<le> p \<and> p \<le> u};
  p \<leftarrow> spmf_of_set \<K>; 
  return_spmf p}) 
  ({p | (p::nat). prime p})) p = 0"
    using cond_spmf_def by auto

  have "
  \<lbrakk>p mod 4 = 3; q mod 4 = 3;
   prime p; prime q;
   r < p * q; m \<noteq> [];
   coprime r (p * q); p \<noteq> q\<rbrakk> \<Longrightarrow>
  decrypt_alt p q (encrypt_alt (p * q) m r) = m"
    using correctness 
    by auto



  have spmf: "spmf (do {p \<leftarrow> spmf_of_set ?\<K>; return_spmf p}) x = indicator ?\<K> x / card ?\<K>" 
    using spmf_of_set by auto
  have "(x \<notin> ?\<K>) = ((indicator ?\<K> x) = 0)" by auto
  then have "(x \<notin> ?\<K>) = (spmf (do {p \<leftarrow> spmf_of_set ?\<K>; return_spmf p}) x = 0)" 
    using spmf by auto
  then have x_in_k_iff: "(x \<in> ?\<K>) = (spmf (do {p \<leftarrow> spmf_of_set ?\<K>; return_spmf p}) x > 0)" 
    unfolding indicator_def by force
  then have "(spmf (do {p \<leftarrow> spmf_of_set ?\<K>; return_spmf p}) x > 0) \<Longrightarrow> prime x" by auto
  from x_in_k_iff have "(spmf (do {p \<leftarrow> spmf_of_set ?\<K>; return_spmf p}) x > 0) \<Longrightarrow> x mod 4 = 3" by auto


  have spmf: "spmf (do {q \<leftarrow> spmf_of_set (?\<K> - {p}) ; return_spmf q}) x = indicator (?\<K> - {p}) x / card (?\<K> - {p})" 
    using spmf_of_set by auto
  have "(x \<notin> (?\<K> - {p})) = ((indicator (?\<K> - {p}) x) = 0)"
    by (auto simp add: indicator_def)
  then have "(x \<notin> (?\<K> - {p})) = (spmf (do {p \<leftarrow> spmf_of_set (?\<K> - {p}); return_spmf p}) x = 0)" 
    using spmf by auto
  then have x_in_k_iff: "(x \<in> (?\<K> - {p})) = (spmf (do {p \<leftarrow> spmf_of_set (?\<K> - {p}); return_spmf p}) x > 0)" 
    unfolding indicator_def by force
  then have "(spmf (do {p \<leftarrow> spmf_of_set (?\<K> - {p}); return_spmf p}) x > 0) \<Longrightarrow> prime x" by auto
  then have "(spmf (do {p \<leftarrow> spmf_of_set (?\<K> - {p}); return_spmf (prime p)})) True = 1" sorry
  (*I CAN'T DO THIS?!*)

  then show "?thesis" sorry
qed

end