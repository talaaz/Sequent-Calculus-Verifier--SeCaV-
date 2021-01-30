theory s184235 imports SeCaV begin

\<comment> \<open>Please keep each line shorter than 100 characters and do not modify the above "imports" at all\<close>

(*

*)


\<comment> \<open>Please keep the "end" command and ensure that Isabelle2020 does not indicate any errors at all\<close>

section \<open>Problem 1\<close>

proposition \<open>(\<exists>x. \<forall>y. p x y) \<longrightarrow> (\<forall>y. \<exists>x. p x y)\<close> by metis

lemma  \<open>\<tturnstile>
  [
    Imp 
    (Exi (Uni ( Pre 0 [Var 1, Var 0])) )
    (Uni(Exi ( Pre 0 [Var 0, Var 1]))) 
  ]
  \<close>
proof -
   from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Exi (Uni ( Pre 0 [Var 1, Var 0])) ),
      (Uni(Exi ( Pre 0 [Var 0, Var 1]))) 
    ]
    \<close>
     using that by simp

 with DeltaExi have ?thesis if \<open>\<tturnstile>
    [
      Neg (Uni ( Pre 0 [Fun 0[], Var 0 ])) ,
      (Uni(Exi ( Pre 0 [Var 0, Var 1]))) 
    ]
    \<close>
   using that by simp

  with Ext have ?thesis if \<open>\<tturnstile>
    [
      (Uni(Exi ( Pre 0 [Var 0, Var 1]))) ,
      Neg (Uni ( Pre 0 [Fun 0[], Var 0 ]))
    ]
    \<close>
    using that by simp

  with DeltaUni have ?thesis if \<open>\<tturnstile>
    [
      Exi(Pre 0 [Var 0, Fun 1 [] ]),
      Neg (Uni ( Pre 0 [Fun 0[], Var 0 ]))
    ]
    \<close>
    using that by simp

  with GammaExi[where t=\<open>Fun 0 []\<close>] have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 [], Fun 1 []],
      Neg (Uni ( Pre 0 [Fun 0[], Var 0 ]))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Neg (Uni ( Pre 0 [Fun 0[], Var 0 ])),
      Pre 0 [Fun 0 [], Fun 1 []]
    ]
    \<close>
    using that by simp

 with GammaUni have ?thesis if \<open>\<tturnstile>
    [
      Neg ( Pre 0 [Fun 0[], Fun 1[] ]),
      Pre 0 [Fun 0 [], Fun 1 []]
    ]
    \<close>
    using that by simp

 with Ext have ?thesis if \<open>\<tturnstile>
    [
 Pre 0 [Fun 0 [], Fun 1 []],
      Neg ( Pre 0 [Fun 0[], Fun 1[] ])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

section \<open>Problem 2\<close>

theorem \<open>let x = size ''

It is 100% optional to answer and has no influence on the assessment.

Explain in a few words your overall impression of Isabelle and SeCaV:

'' in 111 < x \<and> x < 999\<close> proof auto qed proposition undefined oops

end
