theory BG_formalization imports
  Main
  BG_aux
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
definition key_gen :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> (nat \<times> nat))" where 
  "key_gen p q = (p * q, (p, q))"

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
  "split m n = (take n m) # (split (drop n m) n)"

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



fun enc_loop_func_between 
  :: "((nat  => bitstring) \<times> nat \<times> nat \<times> bitstring list) \<Rightarrow> bitstring list \<Rightarrow> nat \<Rightarrow> bitstring list" 
  where
   "enc_loop_func_between (f, n, h, []) c_acc x = rev c_acc" |
   "enc_loop_func_between (f, n, h, (m_i # m_rest)) c_acc x =
        (let x_i = x * x mod n in
        let p_i = f (x_i mod 2^h) in
        let c_i = m_i [\<oplus>] p_i in
        enc_loop_func_between (f, n, h, m_rest) (c_i # c_acc) x_i
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
    (let d_p = ((Suc p) div 4) ^ (Suc t) mod (p - 1) in d_p)"

fun merge_list :: "'a list list => 'a list" where
  "merge_list [] = []" |
  "merge_list (x # xs) = x @ (merge_list xs)"

definition decrypt :: "nat \<Rightarrow> nat \<Rightarrow> (bitstring list \<times> nat) \<Rightarrow> bitstring" where
  "decrypt p q tup = (case tup of (c, x) \<Rightarrow> 
   (let u_p = x ^ (calculate_exponent (length c) p) mod p in
    let u_q = x ^ (calculate_exponent (length c) q) mod q in
    let ((r_p, r_q), _) = euclid_ext (int p) (int q) in
    let x_0 = nat ((int u_p * r_p * int p + int u_p * r_q * int q) mod (p * q)) in
    let (m, x') = enc_loop (p * q, (nat \<lfloor>log 2 (log 2 (p * q))\<rfloor>) , c) x_0 in
    merge_list m))"

definition decrypt_alt :: "nat \<Rightarrow> nat \<Rightarrow> (bitstring list \<times> nat) \<Rightarrow> bitstring" where
  "decrypt_alt p q tup = (case tup of (c, x) \<Rightarrow> 
   (let (u_p::nat) = x ^ (calculate_exponent (length c) p) mod p in
    let (u_q::nat) = x ^ (calculate_exponent (length c) q) mod q in
    let ((r_p, r_q), _) = euclid_ext (int p) (int q) in
    let x_0 = nat ((u_q * r_p * p + u_p * r_q * q) mod int (p * q)) in
    let (m, x') = enc_loop_alt (p * q, (nat \<lfloor>log 2 (log 2 (p * q))\<rfloor>) , c) x_0 in
    merge_list m))"

end