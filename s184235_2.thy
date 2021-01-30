theory s184235_2 imports SeCaV begin

\<comment> \<open>Please keep each line shorter than 100 characters and do not modify the above "imports" at all\<close>

(*
  Solutions must be entered directly in this file instead of $$$$$ such that there are no errors.

  IT IS ONLY ALLOWED TO REPLACE $$$$$ WITH LEMMA/PROOF - ABSOLUTELY NO OTHER CHANGES ARE ALLOWED.

  This comment can be removed and of course the theory name should be changed to your student id. 
*)

abbreviation \<open>P \<equiv> Pre 0 []\<close>

abbreviation \<open>Q \<equiv> Pre 1 []\<close>

section \<open>Problem 1\<close>

proposition \<open>p \<and> q \<longrightarrow> q \<and> p\<close> by metis

lemma  \<open>\<tturnstile>
  [
    Imp (Con P Q)  (Con Q P)
  ]
  \<close>
proof -
  from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Con P Q),
      (Con Q P)
    ]
    \<close>
    using that by simp

  with AlphaCon have ?thesis if \<open>\<tturnstile>
    [
      Neg P,
      Neg Q,
      Con Q P
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Con Q P,
      Neg P, 
      Neg Q
    ]
    \<close>
    using that by simp
  with BetaCon have ?thesis if \<open>\<tturnstile>
    [
      Q,
      Neg P,
      Neg Q
    ]
    \<close> and  \<open>\<tturnstile>
    [
      P,
      Neg P,
      Neg Q
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Q,
      Neg Q
    ]
    \<close> and  \<open>\<tturnstile>
    [
      P,
      Neg P
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

\<comment> \<open>Please keep the "end" command and ensure that Isabelle2020 does not indicate any errors at all\<close>

end
