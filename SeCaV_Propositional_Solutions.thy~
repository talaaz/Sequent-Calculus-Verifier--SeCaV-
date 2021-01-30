theory SeCaV_Propositional_Solutions imports SeCaV_Propositional begin

section \<open>Exercise 1\<close>

proposition \<open>p \<and> q \<longrightarrow> p\<close> by metis

lemma \<open>\<tturnstile>
  [
    Imp (Con P Q) P
  ]
  \<close>
proof -
  from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Con P Q),
      P
    ]
    \<close>
    using that by simp
  with AlphaCon have ?thesis if \<open>\<tturnstile>
    [
      Neg P,
      Neg Q,
      P
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      P,
      Neg P
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

section \<open>Exercise 2\<close>

proposition \<open>p \<and> q \<longrightarrow> q\<close> by metis

lemma \<open>\<tturnstile>
  [
    Imp (Con P Q) Q
  ]
  \<close>
proof -
  from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Con P Q),
      Q
    ]
    \<close>
    using that by simp
  with AlphaCon have ?thesis if \<open>\<tturnstile>
    [
      Neg P,
      Neg Q,
      Q
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Q,
      Neg Q
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

section \<open>Exercise 3\<close>

proposition \<open>(p \<longrightarrow> q) \<or> (q \<longrightarrow> r)\<close> by metis

lemma \<open>\<tturnstile>
  [
    Dis (Imp P Q) (Imp Q R)
  ]
  \<close>
proof -
  from AlphaDis have ?thesis if \<open>\<tturnstile>
    [
      Imp P Q,
      Imp Q R
    ]
    \<close>
    using that by simp
  with AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg P,
      Q,
      Imp Q R
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Imp Q R,
      Q
    ]
    \<close>
    using that by simp
  with AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg Q,
      R,
      Q
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Q,
      Neg Q
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

section \<open>Exercise 4\<close>

proposition \<open>(p \<longrightarrow> q) \<longrightarrow> p \<longrightarrow> q\<close> by metis

lemma \<open>\<tturnstile>
  [
    Imp (Imp P Q) (Imp P Q)
  ]
  \<close>
proof -
  from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp P Q),
      Imp P Q
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Imp P Q,
      Neg (Imp P Q)
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

section \<open>Exercise 5\<close>

proposition \<open>p \<longrightarrow> (p \<longrightarrow> q) \<longrightarrow> q\<close> by metis

lemma \<open>\<tturnstile>
  [
    Imp P (Imp (Imp P Q) Q)
  ]
  \<close>
proof -
  from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg P,
      Imp (Imp P Q) Q
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Imp (Imp P Q) Q,
      Neg P
    ]
    \<close>
    using that by simp
  with AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp P Q),
      Q,
      Neg P
    ]
    \<close>
    using that by simp
  with BetaImp have ?thesis if \<open>\<tturnstile>
    [
      P,
      Q,
      Neg P
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg Q,
      Q,
      Neg P
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
      Q,
      Neg Q
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

section \<open>Exercise 6\<close>

proposition \<open>p \<and> (p \<longrightarrow> q) \<longrightarrow> q\<close> by metis

lemma \<open>\<tturnstile>
  [
    Imp (Con P (Imp P Q)) Q
  ]
  \<close>
proof -
  from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Con P (Imp P Q)),
      Q
    ]
    \<close>
    using that by simp
  with AlphaCon have ?thesis if \<open>\<tturnstile>
    [
      Neg P,
      Neg (Imp P Q),
      Q
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp P Q),
      Neg P,
      Q
    ]
    \<close>
    using that by simp
  with BetaImp have ?thesis if \<open>\<tturnstile>
    [
      P,
      Neg P,
      Q
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg Q,
      Neg P,
      Q
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
      Q,
      Neg Q
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

section \<open>Exercise 7\<close>

proposition \<open>p \<longrightarrow> q \<longrightarrow> p\<close> by metis

lemma \<open>\<tturnstile>
  [
    Imp P (Imp Q P)
  ]
  \<close>
proof -
  from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg P,
      Imp Q P
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Imp Q P,
      Neg P
    ]
    \<close>
    using that by simp
  with AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg Q,
      P,
      Neg P
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      P,
      Neg P
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

section \<open>Exercise 8\<close>

proposition \<open>(p \<longrightarrow> q \<longrightarrow> r) \<longrightarrow> (p \<longrightarrow> q) \<longrightarrow> p \<longrightarrow> r\<close> by metis

lemma \<open>\<tturnstile>
  [
    Imp (Imp P (Imp Q R)) (Imp (Imp P Q) (Imp P R))
  ]
  \<close>
proof -
  from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp P (Imp Q R)),
      Imp (Imp P Q) (Imp P R)
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Imp (Imp P Q) (Imp P R),
      Neg (Imp P (Imp Q R))
    ]
    \<close>
    using that by simp
  with AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp P Q),
      Imp P R,
      Neg (Imp P (Imp Q R))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Imp P R,
      Neg (Imp P Q),
      Neg (Imp P (Imp Q R))
    ]
    \<close>
    using that by simp
  with AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg P,
      R,
      Neg (Imp P Q),
      Neg (Imp P (Imp Q R))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp P Q),
      Neg P,
      R,
      Neg (Imp P (Imp Q R))
    ]
    \<close>
    using that by simp
  with BetaImp have ?thesis if \<open>\<tturnstile>
    [
      P,
      Neg P,
      R,
      Neg (Imp P (Imp Q R))
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg Q,
      Neg P,
      R,
      Neg (Imp P (Imp Q R))
    ]
    \<close>
    using that by simp
  with Basic have ?thesis if \<open>\<tturnstile>
    [
      Neg Q,
      Neg P,
      R,
      Neg (Imp P (Imp Q R))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp P (Imp Q R)),
      Neg P,
      Neg Q,
      R
    ]
    \<close>
    using that by simp
  with BetaImp have ?thesis if \<open>\<tturnstile>
    [
      P,
      Neg P,
      Neg Q,
      R
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Imp Q R),
      Neg P,
      Neg Q,
      R
    ]
    \<close>
    using that by simp
  with Basic have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp Q R),
      Neg P,
      Neg Q,
      R
    ]
    \<close>
    using that by simp
  with BetaImp have ?thesis if \<open>\<tturnstile>
    [
      Q,
      Neg P,
      Neg Q,
      R
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg R,
      Neg P,
      Neg Q,
      R
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Q,
      Neg Q
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

section \<open>Exercise 9\<close>

proposition \<open>p \<or> q \<longrightarrow> q \<or> p\<close> by metis

lemma \<open>\<tturnstile>
  [
    Imp (Dis P Q) (Dis Q P)
  ]
  \<close>
proof -
  from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Dis P Q),
      Dis Q P
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Dis Q P,
      Neg (Dis P Q)
    ]
    \<close>
    using that by simp
  with AlphaDis have ?thesis if \<open>\<tturnstile>
    [
      Q,
      P,
      Neg (Dis P Q)
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Neg (Dis P Q),
      P,
      Q
    ]
    \<close>
    using that by simp
  with BetaDis have ?thesis if \<open>\<tturnstile>
    [
      Neg P,
      P,
      Q
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg Q,
      P,
      Q
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
      Q,
      Neg Q
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

end
