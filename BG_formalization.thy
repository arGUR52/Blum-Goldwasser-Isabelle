theory BG_formalization imports
  CryptHOL.CryptHOL
begin

definition key_gen :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
  "key_gen p q = p * q"

type_synonym bitstring = "bool list"

definition encrypt :: "nat \<Rightarrow> bitstring \<Rightarrow> nat \<Rightarrow> bitstring" where
  "encrypt n m r = m" (* TODO: implement encrypt *)