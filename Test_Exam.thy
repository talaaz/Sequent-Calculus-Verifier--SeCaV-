theory Test_Exam imports SeCaV begin

(* REPLACE $$$$$ WITH LEMMA/PROOF *)

lemma  \<open>\<tturnstile>
  [
    Imp (Neg (Neg (Pre 0 [])))  (Pre 0 [])
  ]
  \<close>
proof -
  from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Neg (Neg (Pre 0 []))), 
      (Pre 0 [])
    ]
    \<close>
    using that by simp
  with Neg have ?thesis if \<open>\<tturnstile>
    [ 
      Neg (Pre 0 []),
      Pre 0 []

    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [ 
      Pre 0 [],
      Neg  (Pre 0 [])

    ]
    \<close>
    using that by simp

  with Basic show ?thesis
    by simp
qed

lemma \<open>\<tturnstile>
  [
    Imp (Uni (Pre 0 [Var 0])) (Con (Pre 0 [Fun 0 []]) (Pre 0 [Fun 1 []]))
  ]
  \<close>
proof -
     from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Uni (Pre 0 [Var 0])) ,
      (Con (Pre 0 [Fun 0 []]) (Pre 0 [Fun 1 []]))
    ]
    \<close>
     using that by simp


  with Ext have ?thesis if \<open>\<tturnstile>
    [
  
      Con (Pre 0 [Fun 0 []]) (Pre 0 [Fun 1 []]),
      Neg (Uni (Pre 0 [Var 0])) 
    ]
    \<close>
    using that by simp
  with BetaCon have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 []],
     Neg (Uni (Pre 0 [Var 0]))
    ]
    \<close> and  \<open>\<tturnstile>
    [
      Pre 0 [Fun 1 []] ,
     Neg (Uni (Pre 0 [Var 0]))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Neg (Uni (Pre 0 [Var 0])),
      Pre 0 [Fun 0 []]
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Uni (Pre 0 [Var 0])),
      Pre 0 [Fun 1 []]
    ]
    \<close>
    using that by simp
  with GammaUni have ?thesis if \<open>\<tturnstile>
  [
      Neg (Pre 0 [Fun 0 []]),
      Pre 0 [Fun 0 []]
   
    ]
    \<close> and  \<open>\<tturnstile>
    [
     Neg (Pre 0 [Fun 1[]]),
      Pre 0 [Fun 1 []]
    ]
    \<close>
    using that by simp

  with Ext have ?thesis if \<open>\<tturnstile>
  [      Pre 0 [Fun 0 []],
      Neg (Pre 0 [Fun 0 []])

   
    ]
    \<close> and  \<open>\<tturnstile>
    [      
    Pre 0 [Fun 1 []],
     Neg (Pre 0 [Fun 1[]])

    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp

qed

proposition \<open>p a \<longrightarrow> (\<exists>x. p x)\<close> by metis
lemma \<open>\<tturnstile>
  [
    Imp (Pre 0 [Fun 0[]]) (Exi (Pre 0 [ Var 0]))
  ]
  \<close>
proof -
  from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 0[]]),
      Exi (Pre 0 [ Var 0])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
       Exi (Pre 0 [ Var 0]),
       Neg (Pre 0 [Fun 0[]])
    ]
    \<close>
    using that by simp
 with GammaExi have ?thesis if \<open>\<tturnstile>
    [      
      Pre 0 [ Fun 0[]],
      Neg (Pre 0 [Fun 0[]])
    
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed



proposition \<open>(\<forall>x y. p x y) \<longrightarrow> (\<forall>x. p x x)\<close> by metis
lemma \<open>\<tturnstile>
  [
    Imp (Uni (Uni (Pre 0 [Var 0, Var 1]))) (Uni (Pre 0 [ Var 0,Var 0]))
  ]
  \<close>
proof -
 from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Uni (Uni (Pre 0 [Var 0, Var 1]))),
      Uni (Pre 0 [ Var 0,Var 0])
    ]
    \<close>
   using that by simp

  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Uni (Pre 0 [ Var 0,Var 0]),
      Neg (Uni (Uni (Pre 0 [Var 0, Var 1])))
    ]
    \<close>
    using that by simp
 with DeltaUni have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [ Fun 0 [],Fun 0 []],
      Neg (Uni (Uni (Pre 0 [Var 0, Var 1])))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
       Neg (Uni (Uni (Pre 0 [Var 0, Var 1]))),
       Pre 0 [ Fun 0 [],Fun 0 []]    
    ]
    \<close>
    using that by simp
with GammaUni[where t=\<open>Fun 0 []\<close>] have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 0 [], Fun 0 []]),
       Pre 0 [ Fun 0 [],Fun 0 []]    
    ]
    \<close>
    using that by simp
 with Ext have ?thesis if \<open>\<tturnstile>
    [
            Pre 0 [ Fun 0 [],Fun 0 []]  ,
         Neg (Pre 0 [Fun 0 [], Fun 0 []])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

proposition \<open>p a \<and> (p a \<longrightarrow> (\<forall>x. p x)) \<longrightarrow> (\<forall>x. p x)\<close> by metis
lemma \<open>\<tturnstile>
  [
  Imp 
    (Con (Pre 0 [Fun 0 []])  (Imp (Pre 0 [Fun 0 []]) (Uni (Pre 0 [Var 0]))))
    (Uni (Pre 0 [Var 0]))
  ]
  \<close>
proof -
   from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg  (Con (Pre 0 [Fun 0 []])  (Imp (Pre 0 [Fun 0 []]) (Uni (Pre 0 [Var 0])))),
      Uni (Pre 0 [Var 0])
    ]
    \<close>
     using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
        Neg  (Con (Pre 0 [Fun 0 []])  (Imp (Pre 0 [Fun 0 []]) (Uni (Pre 0 [Var 0])))),
        Uni (Pre 0 [Var 0])
    ]
    \<close>
    using that by simp
  with AlphaCon have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 0 []]),
      Neg (Imp (Pre 0 [Fun 0 []]) (Uni (Pre 0 [Var 0]))),
        Uni (Pre 0 [Var 0])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [     
        Neg (Imp (Pre 0 [Fun 0 []]) (Uni (Pre 0 [Var 0]))),
        Neg (Pre 0 [Fun 0 []]),
        Uni (Pre 0 [Var 0])
    ]
    \<close>
    using that by simp


  with BetaImp have ?thesis if \<open>\<tturnstile>
    [
        Pre 0 [Fun 0 []], 
        Neg (Pre 0 [Fun 0 []]),
        Uni (Pre 0 [Var 0])
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Uni (Pre 0 [Var 0])),
        Neg (Pre 0 [Fun 0 []]),
        Uni (Pre 0 [Var 0])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
        Pre 0 [Fun 0 []], 
        Neg (Pre 0 [Fun 0 []])
    ]
    \<close> and \<open>\<tturnstile>
    [
        Uni (Pre 0 [Var 0]),
        Neg (Uni (Pre 0 [Var 0]))
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed



end
