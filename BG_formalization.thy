theory BG_formalization imports
  Main
  CryptHOL.CryptHOL
  "Crypto_Standards.Words"
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

text "We define the loop in the encryption as a recursive function. This function takes the nat-to-bit 
conversion function as a parameter:"

function enc_loop_func 
  :: "((nat => bitstring) \<times> nat \<times> nat \<times> bitstring list) \<Rightarrow> bitstring list \<Rightarrow> nat \<Rightarrow> (bitstring list \<times> nat)" 
  where
   "enc_loop_func (f, n, h, []) c_acc x = (c_acc, x)" |
   "enc_loop_func (f, n, h, (m_i # m_rest)) c_acc x = do
        {
        let x_i = x * x mod n;
        let p_i = f (x_i mod 2^h);
        let c_i = m_i [\<oplus>] p_i;
        enc_loop_func (f, n, h, m_rest) (c_i # c_acc) x_i
        }"
  apply (auto)
  using List.list.exhaust by blast

text "The function keyword is needed, since 'fun' didn't allow the function application (f (x_i mod 2^h))."

text "A simple function to convert a bit represented by a natural number to a bit represented by a boolean
value:"

function nat_to_bit :: "nat \<Rightarrow> bool" where
  case_0: "nat_to_bit 0 = False" | 
  case_1: "nat_to_bit 1 = True" |
  case_greater: "nat_to_bit (Suc (Suc n)) = False"
  apply auto
  using not0_implies_Suc by blast

text "The function gives False for anything other than True."

text "We finally define a function to convert a natural number to a bitstring, with the help of nat_to_bits."
definition nat_to_bitstring :: "nat \<Rightarrow> bitstring" where 
  "nat_to_bitstring = (\<lambda>n. map (nat_to_bit) (nat_to_bits n))"

text "Abstracting away from accumulators and conversion functions:"
fun enc_loop 
   :: "(nat \<times> nat \<times> bitstring list) \<Rightarrow> nat \<Rightarrow> (bitstring list \<times> nat)" 
   where
   "enc_loop (n, h, m) x 
    = enc_loop_func (nat_to_bitstring, n, h, m) [] x "

text "At last, the encryption function:"
definition encrypt :: "nat \<Rightarrow> bitstring \<Rightarrow> nat \<Rightarrow> (bitstring list \<times> nat)" where
  "encrypt n m r = 
  do {
  let h = nat \<lfloor>log 2 (log 2 n)\<rfloor>;
  let t = \<lceil>h / (length m)\<rceil>;
  let m_l = split m h;
  let (x_0 :: nat) = (r * r) mod n;
  let (c, x_t) = enc_loop (n, h, m_l) x_0;
  let x_t' = x_t * x_t mod n;
  (c, x_t')}"

(* TODO: Clean everything out! E.g. put supporting auxiliary functions to BG_aux.thy.  *)
(* TODO: Ask about clean coding principles - this seems clunky, is it really ok?*)
(* TODO: Check if this works as intended! - But how? *)
