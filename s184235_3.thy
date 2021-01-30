theory s184235_3 imports SeCaV begin

\<comment> \<open>Please keep each line shorter than 100 characters and do not modify the above "imports" at all\<close>

(*
  Solutions must be entered directly in this file instead of $$$$$ such that there are no errors.

  IT IS ONLY ALLOWED TO REPLACE $$$$$ WITH LEMMA/PROOF - ABSOLUTELY NO OTHER CHANGES ARE ALLOWED.

  This comment can be removed and of course the theory name should be changed to your student id.
*)

abbreviation \<open>P \<equiv> Pre 0 []\<close>

abbreviation \<open>Q \<equiv> Pre 1 []\<close>

abbreviation \<open>R \<equiv> Pre 2 []\<close>

section \<open>Problem 1\<close>

proposition \<open>(p \<longrightarrow> q) \<longrightarrow> p \<or> r \<longrightarrow> q \<or> r\<close> by metis

lemma \<open>\<tturnstile>
  [
    Imp (Imp P Q) (Imp (Dis P R) (Dis Q R))
  ]
  \<close>
proof -
   from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp P Q),
      Imp (Dis P R) (Dis Q R)
    ]
    \<close>
     using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Imp (Dis P R) (Dis Q R),
      Neg (Imp P Q)
    ]
    \<close>
    using that by simp
  with AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Dis P R),
      (Dis Q R),
      Neg (Imp P Q)
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Dis Q R,
      Neg (Imp P Q),
      Neg (Dis P R)    
    ]
    \<close>
    using that by simp
  with AlphaDis have ?thesis if \<open>\<tturnstile>
    [
      Q,
      R,
      Neg (Imp P Q),
      Neg (Dis P R) 
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp P Q),
      Q,
      R,
      Neg (Dis P R)
    ]
    \<close>
    using that by simp

  with BetaImp have ?thesis if \<open>\<tturnstile>
    [
      P,
      Q,
      R,
      Neg (Dis P R)
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg Q,
      Q,
      R,
      Neg (Dis P R)
    ]
    \<close>
    using that by simp
 
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      P,
      Q,
      R,
      Neg (Dis P R)
    ]
    \<close> and \<open>\<tturnstile>
    [
      Q,
      R,
      Neg Q,
      Neg (Dis P R)
    ]
    \<close>
    using that by simp

  with Basic have ?thesis if \<open>\<tturnstile>
   [     
      P,
      Q,
      R,
      Neg (Dis P R)
    ]
    \<close>
    using that by simp

  with Ext have ?thesis if \<open>\<tturnstile>
   [   
      Neg (Dis P R),  
      P,
      Q,
      R
    ]
    \<close>
    using that by simp

  with BetaDis have ?thesis if \<open>\<tturnstile>
   [     
      Neg P,
      P,
      Q,
      R
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg R,      
      P,
      Q,
      R
    ]
    \<close>
    using that by simp

  with Ext have ?thesis if \<open>\<tturnstile>
    [
      P,
      Neg P
    ]
    \<close> and \<open>\<tturnstile>
    [
      R,
      Neg R
    ]
    \<close>
    using that by simp

  with Basic show ?thesis
    by simp
qed

\<comment> \<open>Please keep the "end" command and ensure that Isabelle2020 does not indicate any errors at all\<close>

end
