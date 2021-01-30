theory Exam imports SeCaV begin

(* S184235 *)

lemma  \<open>\<tturnstile>
  [
    Dis (Neg (Pre 0 []))  (Pre 0 [])
  ]
  \<close>
proof -
   from AlphaDis have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 []),
      Pre 0 []
    ]
    \<close>
     using that by simp
 with Ext have ?thesis if \<open>\<tturnstile>
    [     
      Pre 0 [],
      Neg (Pre 0 [])

    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

lemma   \<open>\<tturnstile>
  [
    Imp (Neg(Uni (Pre 0 [Var 0]))) (Exi(Neg (Pre 0 [Var 0])))
  ]
  \<close>
proof -
     from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Neg(Uni (Pre 0 [Var 0]))),
      (Exi(Neg (Pre 0 [Var 0])))
    ]
    \<close>
       using that by simp
  with Neg have ?thesis if \<open>\<tturnstile>
    [ 
      Uni (Pre 0 [Var 0]),
      Exi(Neg (Pre 0 [Var 0]))

    ]
    \<close>
    using that by simp
  with DeltaUni have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 0[]],
      Exi(Neg (Pre 0 [Var 0]))
    ]
    \<close>
    using that by simp

 with Ext have ?thesis if \<open>\<tturnstile>
    [     
      Exi(Neg (Pre 0 [Var 0])),
      Pre 0 [Fun 0[]]
    ]
    \<close>
   using that by simp
  with GammaExi[where t=\<open>Fun 0 []\<close>] have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 0 []]),
      Pre 0 [Fun 0[]]    
    ]
    \<close>
    using that by simp
 with Ext have ?thesis if \<open>\<tturnstile>
    [     
      Pre 0 [Fun 0[]],
      Neg (Pre 0 [Fun 0 []])    
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

end
