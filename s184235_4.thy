theory s184235_4 imports SeCaV begin

\<comment> \<open>Please keep each line shorter than 100 characters and do not modify the above "imports" at all\<close>

section \<open>Problem 1\<close>

proposition \<open>(\<forall>x. p x) \<longrightarrow> p a\<close> by metis

lemma  \<open>\<tturnstile>
  [
    Imp (Uni (Pre 0[Var 0]))  (Pre 0 [Fun 0 []])
  ]
  \<close>
proof -
  from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
       Neg (Uni (Pre 0[Var 0])),
       Pre 0 [Fun 0 []]
    ]
    \<close>
      using that by simp
  with GammaUni[where t=\<open>Fun 0 []\<close>] have ?thesis if \<open>\<tturnstile>
    [
       Neg (Pre 0[Fun 0 []]),
       Pre 0 [Fun 0 []]
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
       Pre 0 [Fun 0 []],
       Neg (Pre 0[Fun 0 []])
      
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

section \<open>Problem 2\<close>

proposition \<open>p a a \<longrightarrow> (\<exists>x y. p x y)\<close> by metis

lemma  \<open>\<tturnstile>
  [
    Imp (Pre 0 [Fun 0 [],Fun 0[]]) (Exi(Exi (Pre 0[Var 1, Var 0]))) 
  ]
  \<close>
proof -
     from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
       Neg (Pre 0 [Fun 0 [],Fun 0[]]),
       Exi(Exi (Pre 0[Var 1, Var 0]))
    ]
    \<close>
       using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Exi(Exi (Pre 0[Var 1, Var 0])),
      Neg (Pre 0 [Fun 0 [],Fun 0[]])
    ]
    \<close>
    using that by simp
  with GammaExi[where t=\<open>Fun 0 []\<close>] have ?thesis if \<open>\<tturnstile>
    [
      Pre 0[Fun 0 [], Fun 0[]],
      Neg (Pre 0 [Fun 0 [],Fun 0[]])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

section \<open>Problem 3\<close>

proposition \<open>(\<forall>x. p x) \<and> (\<forall>x. q x) \<longrightarrow> (\<forall>x. p x \<and> q x)\<close> by metis

lemma \<open>\<tturnstile>
  [
    Imp
      (Con (Uni (Pre 0 [Var 0])) (Uni (Pre 1 [Var 0])))
      (Uni (Con (Pre 0 [Var 0]) (Pre 1 [Var 0])))
  ]
  \<close>
proof -
    from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Con (Uni (Pre 0 [Var 0])) (Uni (Pre 1 [Var 0]))),
      Uni (Con (Pre 0 [Var 0]) (Pre 1 [Var 0]))
    ]
    \<close>
      using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
     Uni (Con (Pre 0 [Var 0]) (Pre 1 [Var 0])),
     Neg (Con (Uni (Pre 0 [Var 0])) (Uni (Pre 1 [Var 0])))
    ]
    \<close>
    using that by simp
  with DeltaUni have ?thesis if \<open>\<tturnstile>
    [
     Con (Pre 0 [Fun 0 [] ]) (Pre 1 [Fun 0[]]),
     Neg (Con (Uni (Pre 0 [Var 0])) (Uni (Pre 1 [Var 0])))
    ]
    \<close>
    using that by simp
  with BetaCon have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 [] ],
      Neg (Con (Uni (Pre 0 [Var 0])) (Uni (Pre 1 [Var 0])))
    ]
    \<close> and \<open>\<tturnstile>
    [
      Pre 1 [Fun 0[]],
      Neg (Con (Uni (Pre 0 [Var 0])) (Uni (Pre 1 [Var 0])))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Neg (Con (Uni (Pre 0 [Var 0])) (Uni (Pre 1 [Var 0]))),
      Pre 0 [Fun 0 []]
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Con (Uni (Pre 0 [Var 0])) (Uni (Pre 1 [Var 0]))),
      Pre 1 [Fun 0 []]
    ]
    \<close>
    using that by simp
  with AlphaCon have ?thesis if \<open>\<tturnstile>
    [
      Neg (Uni (Pre 0 [Var 0])) ,
      Neg (Uni (Pre 1 [Var 0])),
      Pre 0 [Fun 0 []]
    ]\<close> and \<open>\<tturnstile>
    [
      Neg (Uni (Pre 0 [Var 0])),
      Neg (Uni (Pre 1 [Var 0])),
      Pre 1 [Fun 0 []]
    ]
    \<close>
    using that by simp
 with Ext have ?thesis if \<open>\<tturnstile>
  [
      Neg (Uni (Pre 0 [Var 0])) ,
      Neg (Uni (Pre 1 [Var 0])),
      Pre 0 [Fun 0 []]
    ]\<close> and \<open>\<tturnstile>
    [
      Neg (Uni (Pre 0 [Var 0])),
      Neg (Uni (Pre 1 [Var 0])),
      Pre 1 [Fun 0 []]
    ]
    \<close>
    using that by simp
  with GammaUni[where t=\<open>Fun 0 []\<close>] have ?thesis if \<open>\<tturnstile>
  [
      Neg (Pre 0 [Fun 0 [] ]) ,
      Neg (Uni (Pre 1 [Var 0])),
      Pre 0 [Fun 0 []]
    ]\<close> and \<open>\<tturnstile>
    [
      Neg  (Pre 0 [Fun 0 []]),
      Neg (Uni (Pre 1 [Var 0])),
      Pre 1 [Fun 0 []]
    ]
    \<close>
    using that by simp
 with Ext have ?thesis if \<open>\<tturnstile>
  [
      Neg (Uni (Pre 1 [Var 0])),
      Neg (Pre 0 [Fun 0 [] ]) ,
      Pre 0 [Fun 0 []]
    ]\<close> and \<open>\<tturnstile>
    [
      Neg (Uni (Pre 1 [Var 0])),
      Neg  (Pre 0 [Fun 0[]]),
      Pre 1 [Fun 0 []]
    ]
    \<close>
    using that by simp
  with GammaUni[where t=\<open>Fun 0 []\<close>] have ?thesis if \<open>\<tturnstile>
 [
      Neg  (Pre 1  [Fun 0 []] ),
      Neg (Pre 0 [Fun 0 [] ]) ,
      Pre 0 [Fun 0 []]
    ]\<close> and \<open>\<tturnstile>
    [
      Neg  (Pre 1  [Fun 0 []] ),
      Neg  (Pre 0 [Fun 0[]]),
      Pre 1 [Fun 0 []]
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
 [
      Pre 0 [Fun 0 []],
      Neg (Pre 0 [Fun 0 [] ]) 
    ]\<close> and \<open>\<tturnstile>
    [
      Pre 1 [Fun 0 []],
      Neg (Pre 1  [Fun 0 []] )
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp

qed

\<comment> \<open>Please keep the "end" command and ensure that Isabelle2020 does not indicate any errors at all\<close>

end
