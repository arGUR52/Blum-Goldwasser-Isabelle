theory BG_formalization imports
  Main
  "Crypto_Standards.Words"
  "CryptHOL.CryptHOL"
begin

section "Introduction"
text "In this theory, our goal is to formalize the Blum-Goldwasser cryptosystem in a deterministic 
setting. Hence, all the variables that are to be sampled from an oracle are given to the following
functions as parameters."

section "Key generation"
text "The key generation process normally picks out two positive integers congruent to 3 mod 4 
(where these two integers are the private key) and multiplies the two to create the public key n."
definition key_gen :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
  "key_gen p q = p * q"

section "Encryption"

text "Before formalizing the encryption process, we define our bitstrings as follows:"

type_synonym bitstring = "bool list"

text "This means that we represent bitstrings as a list of boolean values, True for 1 and False for
0. The bitstrings are represented from most significant to least significant in the list (i.e.
44 = 101011 = [True, False, True, False, True, True]). "

text "We then need a function to split our plaintext message into h-bit blocks. We define the 
following function for this reason:"

fun split :: "bitstring \<Rightarrow> nat \<Rightarrow> bitstring list" where
  "split [] n = []" |
  "split m 0 = []" |
  "split (x # xs) n = (take n (x # xs)) # (split (drop n (x # xs)) n)"

text "The function takes the first n elements from the message, puts it to the head of the resulting 
list, and goes on with splitting the rest."

(*TODO: Find lemmas for split to prove its correctness!*)

text "We define the loop in the encryption as a recursive function. This function takes the nat-to
-bit conversion function as a parameter:"

fun enc_loop_func 
  :: "((nat  => bitstring) \<times> nat \<times> nat \<times> bitstring list) \<Rightarrow> bitstring list \<Rightarrow> nat \<Rightarrow> (bitstring list \<times> nat)" 
  where
   "enc_loop_func (f, n, h, []) c_acc x = (rev c_acc, x)" |
   "enc_loop_func (f, n, h, (m_i # m_rest)) c_acc x =
        (let x_i = x * x mod n in
        let p_i = f (x_i mod 2^h) in
        let c_i = m_i [\<oplus>] p_i in
        enc_loop_func (f, n, h, m_rest) (c_i # c_acc) x_i
        )"

fun enc_loop_func_list 
  :: "((nat  => bitstring) \<times> nat \<times> nat \<times> bitstring list) \<Rightarrow> nat \<Rightarrow> bitstring list" 
  where
   "enc_loop_func_list (f, n, h, []) x = []" |
   "enc_loop_func_list (f, n, h, (m_i # m_rest)) x =
        (let x_i = x * x mod n in
        let p_i = f (x_i mod 2^h) in
        let c_i = m_i [\<oplus>] p_i in
        c_i # enc_loop_func_list (f, n, h, m_rest) x_i
        )"
fun enc_loop_func_x 
  :: "((nat  => bitstring) \<times> nat \<times> nat \<times> nat) \<Rightarrow> nat \<Rightarrow> nat" 
  where
   "enc_loop_func_x (f, n, h, t) x = x ^ (2 ^ t) mod n" 



text "A simple function to convert a bit represented by a natural number to a bit represented by a 
boolean value:"

fun nat_to_bit :: "nat \<Rightarrow> bool" where
  case_0: "nat_to_bit 0 = False" | 
  case_1: "nat_to_bit (Suc 0) = True" |
  case_greater: "nat_to_bit (Suc (Suc n)) = False"




text "The function gives False for anything other than True."

text "We finally define a function to convert a natural number to a bitstring, with the help of 
nat_to_bits."
definition nat_to_bitstring :: "nat \<Rightarrow> nat \<Rightarrow> bitstring" where 
  "nat_to_bitstring = (\<lambda>l n. map (nat_to_bit) (nat_to_bits_len n l))"

text "Abstracting away from accumulators and conversion functions:"
fun enc_loop 
   :: "(nat \<times> nat \<times> bitstring list) \<Rightarrow> nat \<Rightarrow> (bitstring list \<times> nat)" 
   where
   "enc_loop (n, h, m) x 
    = enc_loop_func (nat_to_bitstring h, n, h, m) [] x"

fun enc_loop_alt 
   :: "(nat \<times> nat \<times> bitstring list) \<Rightarrow> nat \<Rightarrow> (bitstring list \<times> nat)" 
   where
   "enc_loop_alt (n, h, m) x 
    = (enc_loop_func_list (nat_to_bitstring h, n, h, m) x, 
      enc_loop_func_x (nat_to_bitstring h, n, h, length m) x)"


text "At last, the encryption function:"
definition encrypt :: "nat \<Rightarrow> bitstring \<Rightarrow> nat \<Rightarrow> (bitstring list \<times> nat)" where
  "encrypt n m r = (
  let h = nat \<lfloor>log 2 (log 2 n)\<rfloor> in 
  let m_l = split m h in 
  let (x_0 :: nat) = (r * r) mod n in 
  let (c, x_t) = enc_loop (n, h, m_l) x_0 in 
  let x_t' = x_t * x_t mod n in 
  (c, x_t'))"

definition encrypt_alt :: "nat \<Rightarrow> bitstring \<Rightarrow> nat \<Rightarrow> (bitstring list \<times> nat)" where
  "encrypt_alt n m r = (
  let h = nat \<lfloor>log 2 (log 2 n)\<rfloor> in 
  let m_l = split m h in 
  let (x_0 :: nat) = (r * r) mod n in 
  let (c, x_t) = enc_loop_alt (n, h, m_l) x_0 in 
  let x_t' = x_t * x_t mod n in 
  (c, x_t'))"







text "An alternate definition of floor log:"

fun floor_nat_log_rec :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "floor_nat_log_rec 0 n acc = 0" |
  "floor_nat_log_rec (Suc 0) n acc = 0" |
  "floor_nat_log_rec base 0 0 = 0" | 
  "floor_nat_log_rec base 0 (Suc acc) = acc" | 
  "floor_nat_log_rec base (Suc n) acc 
    = floor_nat_log_rec base ((Suc n) div base) (Suc acc)"

definition floor_nat_log :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "floor_nat_log base n = floor_nat_log_rec base n 0" 

definition encrypt_discrete_log :: "nat \<Rightarrow> bitstring \<Rightarrow> nat \<Rightarrow> (bitstring list \<times> nat)" where
  "encrypt_discrete_log n m r = (
  let h = (floor_nat_log 2 (floor_nat_log 2 n)) in 
  let m_l = split m h in 
  let (x_0 :: nat) = (r * r) mod n in 
  let (c, x_t) = enc_loop (n, h, m_l) x_0 in 
  let x_t' = x_t * x_t mod n in 
  (c, x_t'))"








text "now the decryption..."

fun calculate_exponent :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
  "calculate_exponent t p = 
    (let d_p = ((Suc p) div 4)^(Suc t) mod (p-1) in d_p)"

fun merge_list :: "'a list list => 'a list" where
  "merge_list [] = []" |
  "merge_list (x # xs) = x @ (merge_list xs)"

definition decrypt :: "nat \<Rightarrow> nat \<Rightarrow> (bitstring list \<times> nat) \<Rightarrow> bitstring" where
  "decrypt p q tup = (case tup of (c, x) \<Rightarrow> 
   (let u_p = x ^ (calculate_exponent (length c) p) in
    let u_q = x ^ (calculate_exponent (length c) q) in
    let ((r_p, r_q), _) = euclid_ext p q in
    let x_0 = nat (u_p * r_p * p + u_q * r_q * q mod (p * q)) in
    let (m, x') = enc_loop (p * q, (nat \<lfloor>log 2 (log 2 (p * q))\<rfloor>) , c) x_0 in
    merge_list m))"

definition decrypt_alt :: "nat \<Rightarrow> nat \<Rightarrow> (bitstring list \<times> nat) \<Rightarrow> bitstring" where
  "decrypt_alt p q tup = (case tup of (c, x) \<Rightarrow> 
   (let u_p = x ^ (calculate_exponent (length c) p) in
    let u_q = x ^ (calculate_exponent (length c) q) in
    let ((r_p, r_q), _) = euclid_ext p q in
    let x_0 = nat (u_p * r_p * p + u_q * r_q * q mod (p * q)) in
    let (m, x') = enc_loop_alt (p * q, (nat \<lfloor>log 2 (log 2 (p * q))\<rfloor>) , c) x_0 in
    merge_list m))"











text "Correctness proof"

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


lemma same_x_0:
  assumes 
    "p mod 4 = 3" "q mod 4 = 3" (*pq_cong_3*)
    "prime p" "prime q" (*pq_prime*)
    "r < p * q" 
  shows "
    let x = r ^ (t + 1) mod (p * q) in
    let u_p = x ^ (calculate_exponent t p) in
    let u_q = x ^ (calculate_exponent t q) in
    let ((r_p, r_q), _) = euclid_ext p q in
    nat (u_p * r_p * p + u_q * r_q * q mod (p * q)) = (r * r) mod n"
proof - 

  show ?thesis sorry
qed 


theorem 
  assumes 
    "p mod 4 = 3" "q mod 4 = 3" (*pq_cong_3*)
    "prime p" "prime q" (*pq_prime*)
    "r < n" "m \<noteq> []"
  shows "decrypt p q (encrypt (p * q) m r) = m"
proof - 
  from encrypt_def have "encrypt (p * q) m r = (
  let h = nat \<lfloor>log 2 (log 2 (p * q))\<rfloor> in 
  let m_l = split m h in 
  let (x_0 :: nat) = (r * r) mod (p * q) in 
  let (c, x_t) = enc_loop (p * q, h, m_l) x_0 in 
  let x_t' = x_t * x_t mod (p * q) in 
  (c, x_t'))"
    by auto
  then have "fst (encrypt (p * q) m r) 
  = fst (let h = nat \<lfloor>log 2 (log 2 (p * q))\<rfloor> in 
  let m_l = split m h in 
  let x_0 = (r * r) mod (p * q) in enc_loop (p * q, h, m_l) x_0)" 
    using prod.exhaust prod.sel(1) prod.simps(2)
    by (metis (mono_tags, lifting))

  have "\<exists>c x. (encrypt (p * q) m r = (c, x))" using encrypt_def surj_pair by 
  by auto
  then obtain c x where "(encrypt (p * q) m r = (c, x))" by blast
  then have "decrypt p q (encrypt (p * q) m r) = decrypt p q (c, x)" by auto
  hence "decrypt p q (encrypt (p * q) m r) =  
   (let u_p = x ^ (calculate_exponent (length c) p) in
    let u_q = x ^ (calculate_exponent (length c) q) in
    let ((r_p, r_q), _) = euclid_ext p q in
    let x_0 = nat (u_p * r_p * p + u_q * r_q * q mod (p * q)) in
    let (m, x') = enc_loop (p * q, (nat \<lfloor>log 2 (log 2 (p * q))\<rfloor>) , c) x_0 in
    merge_list m)" using decrypt_def by auto  

   show ?thesis sorry
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
    by (auto simp add: xor_list_inverse)

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

(* TODO: Clean everything out! E.g. put supporting auxiliary functions to BG_aux.thy.  *)
(* TODO: Check if this works as intended! - But how? *)
