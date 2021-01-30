theory SeCaV_Exercises imports SeCaV begin

section \<open>Exercise 1\<close>

proposition \<open>p a \<longrightarrow> (\<exists>x. p x)\<close> by metis
lemma \<open>\<tturnstile>
  [
    Imp (Pre 0 [Fun 0 []]) (Exi (Pre 0 [Var 0]))
  ]
  \<close>
proof -
  from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg  (Pre 0 [Fun 0 []]),
      (Exi (Pre 0 [Var 0]))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
     
      Exi (Pre 0 [Var 0]), 
      Neg  (Pre 0 [Fun 0 []])
    ]
    \<close>
    using that by simp
  with GammaExi have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 []],
      Neg  (Pre 0 [Fun 0 []])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

section \<open>Exercise 2\<close>

proposition \<open>(\<forall>x y. p x y) \<longrightarrow> (\<forall>x. p x x)\<close> by metis
lemma \<open>\<tturnstile>
  [
    Imp (Uni (Uni (Pre 0 [Var 1, Var 0]))) (Uni (Pre 0 [Var 0, Var 0]))
  ]
  \<close>
proof -
  from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Uni (Uni (Pre 0 [Var 1, Var 0]))) ,
      Uni (Pre 0 [Var 0, Var 0])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Uni (Pre 0 [Var 0, Var 0]),
      Neg (Uni (Uni (Pre 0 [Var 1, Var 0])))
    ]
    \<close>
    using that by simp
  with DeltaUni have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 0[], Fun 0 []],
      Neg (Uni (Uni (Pre 0 [Var 1, Var 0])))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Neg (Uni (Uni (Pre 0 [Var 1, Var 0]))),
      Pre 0 [Fun 0 [], Fun 0 []]
    ]
    \<close>
    using that by simp
  with GammaUni[where t=\<open>Fun 0 []\<close>] have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 0 [], Fun 0 []]),
      Pre 0 [Fun 0 [], Fun 0 []]
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 [], Fun 0 []],
      Neg (Pre 0 [Fun 0 [], Fun 0 []])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed


section \<open>Exercise 3\<close>

proposition \<open>(\<forall>x. p x) \<or> (\<forall>x. q x) \<longrightarrow> (\<forall>x. p x \<or> q x)\<close> by metis

lemma \<open>\<tturnstile>
  [
    Imp
      (Dis (Uni (Pre 0 [Var 0])) (Uni (Pre 1 [Var 0])))
      (Uni (Dis (Pre 0 [Var 0]) (Pre 1 [Var 0])))
  ]
  \<close>
proof -
  from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Dis (Uni (Pre 0 [Var 0])) (Uni (Pre 1 [Var 0]))),
      Uni (Dis (Pre 0 [Var 0]) (Pre 1 [Var 0]))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Uni (Dis (Pre 0 [Var 0]) (Pre 1 [Var 0])),
      Neg (Dis (Uni (Pre 0 [Var 0])) (Uni (Pre 1 [Var 0])))
    ]
    \<close>
    using that by simp
  with DeltaUni have ?thesis if \<open>\<tturnstile>
    [
      Dis (Pre 0 [Fun 0 []]) (Pre 1 [Fun 0 []]),
      Neg (Dis (Uni (Pre 0 [Var 0])) (Uni (Pre 1 [Var 0])))
    ]
    \<close>
    using that by simp
  with AlphaDis have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 []],
      Pre 1 [Fun 0 []],
      Neg (Dis (Uni (Pre 0 [Var 0])) (Uni (Pre 1 [Var 0])))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Neg (Dis (Uni (Pre 0 [Var 0])) (Uni (Pre 1 [Var 0]))),
      Pre 0 [Fun 0 []],
      Pre 1 [Fun 0 []]
    ]
    \<close>
    using that by simp
  with BetaDis have ?thesis if \<open>\<tturnstile>
    [
      Neg (Uni (Pre 0 [Var 0])),
      Pre 0 [Fun 0 []],
      Pre 1 [Fun 0 []]
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Uni (Pre 1 [Var 0])),
      Pre 0 [Fun 0 []],
      Pre 1 [Fun 0 []]
    ]
    \<close>
    using that by simp
  with GammaUni have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 0 []]),
      Pre 0 [Fun 0 []],
      Pre 1 [Fun 0 []]
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Pre 1 [Fun 0 []]),
      Pre 0 [Fun 0 []],
      Pre 1 [Fun 0 []]
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
      Pre 1 [Fun 0 []],
      Neg (Pre 1 [Fun 0 []])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed


section \<open>Exercise 4\<close>

proposition \<open>\<exists>x. \<forall>y. p x \<longrightarrow> p y\<close> by metis

lemma \<open>\<tturnstile>
  [
    Exi (Uni (Imp (Pre 0 [Var 1]) (Pre 0 [Var 0])))
  ]
  \<close>
proof -
  from Ext have ?thesis if \<open>\<tturnstile>
    [
      Exi (Uni (Imp (Pre 0 [Var 1]) (Pre 0 [Var 0]))),
      Exi (Uni (Imp (Pre 0 [Var 1]) (Pre 0 [Var 0])))
    ]
    \<close>
    using that by simp
  with GammaExi[where t=\<open>Fun 0 []\<close>] have ?thesis if \<open>\<tturnstile>
    [
      Uni (Imp (Pre 0 [Fun 0 []]) (Pre 0 [Var 0])),
      Exi (Uni (Imp (Pre 0 [Var 1]) (Pre 0 [Var 0])))
    ]
    \<close>
    using that by simp
  with DeltaUni have ?thesis if \<open>\<tturnstile>
    [
      Imp (Pre 0 [Fun 0 []]) (Pre 0 [Fun 1 []]),
      Exi (Uni (Imp (Pre 0 [Var 1]) (Pre 0 [Var 0])))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Exi (Uni (Imp (Pre 0 [Var 1]) (Pre 0 [Var 0]))),
      Imp (Pre 0 [Fun 0 []]) (Pre 0 [Fun 1 []])
    ]
    \<close>
    using that by simp
  with GammaExi[where t=\<open>Fun 1 []\<close>] have ?thesis if \<open>\<tturnstile>
    [
      Uni (Imp (Pre 0 [Fun 1 []]) (Pre 0 [Var 0])),
      Imp (Pre 0 [Fun 0 []]) (Pre 0 [Fun 1 []])
    ]
    \<close>
    using that by simp
  with DeltaUni have ?thesis if \<open>\<tturnstile>
    [
      Imp (Pre 0 [Fun 1 []]) (Pre 0 [Fun 2 []]),
      Imp (Pre 0 [Fun 0 []]) (Pre 0 [Fun 1 []])
    ]
    \<close>
    using that by simp
  with AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 1 []]),
      Pre 0 [Fun 2 []],
      Imp (Pre 0 [Fun 0 []]) (Pre 0 [Fun 1 []])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Imp (Pre 0 [Fun 0 []]) (Pre 0 [Fun 1 []]),
      Neg (Pre 0 [Fun 1 []])
    ]
    \<close>
    using that by simp
  with AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 0 []]),
      Pre 0 [Fun 1 []],
      Neg (Pre 0 [Fun 1 []])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 1 []],
      Neg (Pre 0 [Fun 1 []])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

section \<open>Exercise 5\<close>

proposition \<open>p a \<and> (p a \<longrightarrow> (\<forall>x. p x)) \<longrightarrow> (\<forall>x. p x)\<close> by metis

lemma \<open>\<tturnstile>
  [
    Imp
      (Con (Pre 0 [Fun 0 []]) (Imp (Pre 0 [Fun 0 []]) (Uni (Pre 0 [Var 0]))))
      (Uni (Pre 0 [Var 0]))
  ]\<close>
proof -
  from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg
        (Con
          (Pre 0 [Fun 0 []])
          (Imp (Pre 0 [Fun 0 []]) (Uni (Pre 0 [Var 0])))),
      Uni (Pre 0 [Var 0])
    ]\<close>
    using that by simp
  with AlphaCon have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 0 []]),
      Neg (Imp (Pre 0 [Fun 0 []]) (Uni (Pre 0 [Var 0]))),
      Uni (Pre 0 [Var 0])
    ]\<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp (Pre 0 [Fun 0 []]) (Uni (Pre 0 [Var 0]))),
      Neg (Pre 0 [Fun 0 []]),
      Uni (Pre 0 [Var 0])
    ]\<close>
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
    ]\<close>
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
    ]\<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

end
