theory DISCARDED_ext_mono_ei
  imports Preliminaries "Wlog.Wlog"
begin

declare[[show_types]]

context order_topology
begin

lemma
  assumes "a < b" 
  shows at_within_Ioo_at_right: "at a within {a<..<b} = at_right a" and
    at_within_Ioo_at_left: "at b within {a<..<b} = at_left b"
  using assms at_within_nhd
   apply (metis inf.right_idem open_lessThan greaterThanLessThan_eq lessThan_iff)
  using assms at_within_nhd
  by (smt (verit, ccfv_SIG) inf.idem inf_aci(1,2)
      greaterThanLessThan_def greaterThan_iff open_greaterThan)

end

(* To be included in Elemenetary_Topology.thy *)
(* analogue for lemma Lim_right_bound *)
lemma Lim_left_bound:
  fixes f :: "'a :: {linorder_topology, conditionally_complete_linorder, no_bot} \<Rightarrow>
    'b :: {linorder_topology, conditionally_complete_linorder}"
  assumes mono: "\<And>a b. a \<in> I \<Longrightarrow> b \<in> I \<Longrightarrow> b < x \<Longrightarrow> a \<le> b \<Longrightarrow> f a \<le> f b"
    and bnd: "\<And>b. b \<in> I \<Longrightarrow> b < x \<Longrightarrow> f b \<le> K"
  shows "(f \<longlongrightarrow> Sup (f ` ({..<x} \<inter> I))) (at x within ({..<x} \<inter> I))"
proof (cases "{..<x} \<inter> I = {}")
  case True
  then show ?thesis by simp
next
  case False
  show ?thesis
  proof (rule order_tendstoI)
    fix b
    assume b: "Sup (f ` ({..<x} \<inter> I)) < b"
    {
      fix y
      assume "y \<in> {..<x} \<inter> I"
      with False bnd have "f y \<le> Sup (f ` ({..<x} \<inter> I))" by (auto intro!: cSup_upper bdd_aboveI2)
      with b have "f y < b" by order
    }
    then show "eventually (\<lambda>x. f x < b) (at x within ({..<x} \<inter> I))"
      by (auto simp: eventually_at_filter intro: exI[of _ 1] zero_less_one)
  next
    fix b
    assume "b < Sup (f ` ({..<x} \<inter> I))"
    from less_cSupD[OF _ this] False obtain y where y: "y < x" "y \<in> I" "b < f y" by auto
    then have "eventually (\<lambda>x. x \<in> I \<longrightarrow> b < f x) (at_left x)"
      unfolding eventually_at_right[OF \<open>y < x\<close>]
      by (smt (verit, best) assms(1) basic_trans_rules(23) eventually_at_left less_le not_le)
    then show "eventually (\<lambda>x. b < f x) (at x within ({..<x} \<inter> I))"
      unfolding eventually_at_filter by eventually_elim simp
  qed
qed

(* analogue for lemma differentiable_transform_within *)
lemma differentiable_transform_open:
  assumes "f differentiable (at x)"
    and "x \<in> s"
    and "open s"
    and "\<And>x'. x'\<in>s \<Longrightarrow> f x' = g x'"
  shows "g differentiable (at x)"
  using assms has_derivative_transform_within_open at_within_open unfolding differentiable_def
  by blast

lemma einterval_empty:
  fixes a b :: ereal
  assumes "a \<ge> b"
  shows "einterval a b = {}"
  using assms einterval_iff by auto

lemma einterval_split:
  fixes a b :: ereal and s::real
  assumes "s \<in> einterval a b"
  shows "einterval a b - {s} = einterval a s \<union> einterval s b"
proof
  show "einterval a b - {s} \<subseteq> einterval a (ereal s) \<union> einterval (ereal s) b"
    using assms einterval_iff by auto
  show "einterval a (ereal s) \<union> einterval (ereal s) b \<subseteq> einterval a b - {s}"
    using assms einterval_iff
    by (smt (verit, ccfv_threshold) Diff_iff Diff_insert_absorb Un_iff
        basic_trans_rules(19) less_ereal.simps(1) subsetI)
qed

(* analogue for lemma einterval_Icc_approximation *)
lemma einterval_Ioc_approximation:
  fixes a b :: ereal
  assumes "a < b"
  obtains u l :: "nat \<Rightarrow> real" where
    "einterval a b = (\<Union>i. {l i <.. u i})"
    "incseq u" "decseq l" "\<And>i. l i < u i" "\<And>i. a < l i" "\<And>i. u i < b"
    "l \<longlonglongrightarrow> a" "u \<longlonglongrightarrow> b"
proof -
  from assms obtain u l :: "nat \<Rightarrow> real" where
    "einterval a b = (\<Union>i. {l i .. u i})"
    "incseq u" "decseq l" "\<And>i. l i < u i" "\<And>i. a < ereal (l i)" "\<And>i. ereal (u i) < b"
    "(\<lambda>i. ereal (l i)) \<longlonglongrightarrow> a" "(\<lambda>i. ereal (u i)) \<longlonglongrightarrow> b"
    using einterval_Icc_approximation by (smt (verit) Sup.SUP_cong)
  moreover have "(\<Union>i. {l i .. u i}) = (\<Union>i. {l i <.. u i})"
  proof
    show "(\<Union>i. {l i .. u i}) \<subseteq> (\<Union>i. {l i <.. u i})"
    proof
      fix x assume "x \<in> (\<Union>i. {l i .. u i})"
      from this obtain i where xi: "x \<in> {l i .. u i}" by blast
      obtain j where "j \<ge> i" "l j < l i"
      proof (cases \<open>a = -\<infinity>\<close>)
        case True
        with \<open>(\<lambda>i. ereal (l i)) \<longlonglongrightarrow> a\<close> obtain k where "l k \<le> ereal (l i - 1)"
          using Lim_MInfty by (meson nle_le)
        hence "l k < l i" by simp
        hence "l (max i k + 1) < l i"
          using \<open>decseq l\<close> by (smt (verit, del_insts) decseq_def le_add1 max.cobounded2)
        moreover have "max i k + 1 \<ge> i" by simp
        ultimately show ?thesis using that by simp
      next
        case False
        with assms obtain ar where aar: "a = ereal ar" by (metis ereal_cases less_ereal.simps(2))
        with \<open>(\<lambda>i. ereal (l i)) \<longlonglongrightarrow> a\<close> have "l \<longlonglongrightarrow> ar" by auto
        moreover have "0 < l i - ar" using \<open>\<And>i. a < ereal (l i)\<close> aar by simp
        ultimately obtain k where "\<And>h. h \<ge> k \<Longrightarrow> norm (l h - ar) < l i - ar"
          using LIMSEQ_D by blast
        hence "\<And>h. h \<ge> k \<Longrightarrow> l h < l i" by force
        hence "l (max i k + 1) < l i" by simp
        moreover have "max i k + 1 \<ge> i" by simp
        ultimately show ?thesis using that by simp
      qed
      hence "x \<in> {l j <.. u j}" using xi assms \<open>incseq u\<close> monoD by fastforce
      thus "x \<in> (\<Union>i. {l i <.. u i})" by blast
    qed
  next
    have "\<And>i. {l i <.. u i} \<subseteq> {l i .. u i}" by force
    thus "(\<Union>i. {l i <.. u i}) \<subseteq> (\<Union>i. {l i .. u i})" by blast
  qed
  ultimately show ?thesis using that by simp
qed

lemma measure_einterval_eqI_Ioc:
  fixes M N :: "real measure" and a b :: ereal
  assumes Mborel: "sets M = sets borel" and Nborel: "sets N = sets borel" and
    "\<And>s t. a < ereal s \<and> s \<le> t \<and> ereal t < b \<Longrightarrow> emeasure M {s<..t} \<noteq> \<infinity>" and
    "\<And>s t. a < ereal s \<and> s \<le> t \<and> ereal t < b \<Longrightarrow> emeasure M {s<..t} = emeasure N {s<..t}"
  shows "restrict_space M (einterval a b) = restrict_space N (einterval a b)"
proof (cases \<open>a < b\<close>)

  case ab: True

  let ?Iab = "einterval a b"
  let ?Iocs = "{{s<..t} | s t :: real. a < ereal s \<and> s \<le> t \<and> ereal t < b}"

  have Iocs_Iab: "?Iocs \<subseteq> Pow ?Iab"
    apply (standard, rewrite Pow_iff, simp, standard)
    by (meson einterval_iff ereal_less_le greaterThanAtMost_iff le_ereal_less less_eq_ereal_def)

  obtain u l :: "nat \<Rightarrow> real" where
    Iab_Un: "?Iab = (\<Union>i. {l i <.. u i})" and
    lu: "\<And>i. l i < u i" and al: "\<And>i. a < l i" and ub: "\<And>i. u i < b"
  using einterval_Ioc_approximation ab by (smt (verit) Inf.INF_cong)

  let ?Iocn = "\<lambda>n::nat. {l n <.. u n}"

  have Iabsigma: "\<And>L :: real measure. sets L = sets borel \<Longrightarrow>
    sets (restrict_space L ?Iab) = sigma_sets ?Iab ?Iocs"
  proof -
    fix L :: "real measure" assume asm: "sets L = sets borel"
    have "sets (restrict_space L ?Iab) = sigma_sets ?Iab ((inter ?Iab) ` {{s<..t} | s t. True})"
      apply (rewrite sets_restrict_space)
      apply (rewrite asm)
      apply (rewrite borel_sigma_sets_Ioc, simp)
      apply (rewrite restricted_sigma; simp?)
       apply (metis Pow_UNIV borel_einterval borel_sigma_sets_Ioc sets_measure_of top_greatest)
      unfolding image_def by simp
    also have "\<dots> = sigma_sets ?Iab ?Iocs"
    proof
      have "(inter ?Iab) ` {{s<..t} | s t. True} \<subseteq> sigma_sets ?Iab ?Iocs"
      proof
        fix A assume "A \<in> (inter ?Iab) ` {{s<..t} | s t. True}"
        from this obtain s t where Aabst: "A = ?Iab \<inter> {s<..t}" by blast
        also have "\<dots> = (\<Union>n. {l n <.. u n} \<inter> {s<..t})" using Aabst Iab_Un by (metis UN_simps(4))
        also have "\<dots> = (\<Union>n. {max (l n) s <.. min (u n) t})" by simp
        moreover have
          "\<And>n. {max (l n) s <.. min (u n) t} \<in> sigma_sets ?Iab ?Iocs"
        proof -
          fix n
          show "{max (l n) s <.. min (u n) t} \<in> sigma_sets ?Iab ?Iocs"
          proof (cases \<open>max (l n) s \<le> min (u n) t\<close>)
            case True
            moreover have "a < ereal (max (l n) s)" using al by (metis less_ereal_le max_def)
            moreover have "ereal (min (u n) t) < b" using ub by (smt (verit) ereal_less_le)
            ultimately have "{max (l n) s <.. min (u n) t} \<in> ?Iocs" by blast
            thus ?thesis ..
          next
            case False
            hence "{max (l n) s <.. min (u n) t} = {}" by auto
            thus ?thesis by (metis sigma_sets.Empty)
          qed
        qed
        ultimately show "A \<in> sigma_sets ?Iab ?Iocs" by (simp add: sigma_sets.Union)
      qed
      thus "sigma_sets ?Iab ((inter ?Iab) ` {{s<..t} | s t. True}) \<subseteq> sigma_sets ?Iab ?Iocs"
        by (rule sigma_sets_mono)
    next
      have "?Iocs \<subseteq> sigma_sets ?Iab ((inter ?Iab) ` {{s<..t} | s t. True})"
      proof
        fix A assume "A \<in> ?Iocs"
        from this obtain s t where "a < ereal s \<and> s \<le> t \<and> ereal t < b" and "A = {s<..t}" by blast
        hence "A = ?Iab \<inter> {s<..t}" using Iocs_Iab by blast
        hence "A \<in> (inter ?Iab) ` {{s<..t} | s t. True}" by auto
        thus "A \<in> sigma_sets ?Iab ((inter ?Iab) ` {{s<..t} | s t. True})" by blast
      qed
      thus "sigma_sets ?Iab ?Iocs \<subseteq> sigma_sets ?Iab ((inter ?Iab) ` {{s<..t} | s t. True})"
        by (rule sigma_sets_mono)
    qed
    finally show "sets (restrict_space L ?Iab) = sigma_sets ?Iab ?Iocs" .
  qed

  have "Int_stable ?Iocs"
  proof (rule Int_stableI)
    fix A B assume "A \<in> ?Iocs" "B \<in> ?Iocs"
    from this obtain sA tA sB tB where
      asA: "a < ereal sA" and sAtA: "sA \<le> tA" and tAb: "ereal tA < b" and "A = {sA <.. tA}" and
      asB: "a < ereal sB" and sBtB: "sB \<le> tB" and eBb: "ereal tB < b" and "B = {sB <.. tB}"
      by blast
    hence AB: "A \<inter> B = {max sA sB <.. min tA tB}" using Int_greaterThanAtMost by blast
    thus "A \<inter> B \<in> ?Iocs"
    proof (cases \<open>max sA sB \<le> min tA tB\<close>)
      case True
      moreover have "a < ereal (max sA sB)" "ereal (min tA tB) < b"
        using asA tAb asB eBb by linarith+
      ultimately show ?thesis using AB by blast
    next
      case False
      hence "A \<inter> B = {}" using AB by force
      thus "A \<inter> B \<in> ?Iocs" using asA less_ereal_le sAtA tAb by fastforce
    qed
  qed
  moreover note Iocs_Iab
  moreover have "\<And>A. A \<in> ?Iocs \<Longrightarrow>
    emeasure (restrict_space M ?Iab) A = emeasure (restrict_space N ?Iab) A"
    apply (rewrite emeasure_restrict_space, simp add: assms)
    using Iocs_Iab apply blast
    apply (rewrite emeasure_restrict_space, simp add: assms)
    using Iocs_Iab apply blast
    using assms by force
  moreover have "sets (restrict_space M ?Iab) = sigma_sets ?Iab ?Iocs" using Iabsigma assms by simp
  moreover have "sets (restrict_space N ?Iab) = sigma_sets ?Iab ?Iocs" using Iabsigma assms by simp
  moreover have rngIocn: "range ?Iocn \<subseteq> ?Iocs"
    using al lu ub by (smt (verit) image_subset_iff mem_Collect_eq)
  moreover have "(\<Union>n. ?Iocn n) = ?Iab" using Iab_Un by simp
  moreover have "\<And>n. emeasure (restrict_space M ?Iab) (?Iocn n) \<noteq> \<infinity>"
    apply (rewrite emeasure_restrict_space, simp add: assms)
    using Iab_Un apply blast
    using assms al lu ub less_imp_le by metis
  ultimately show "restrict_space M ?Iab = restrict_space N ?Iab"
    by (rule measure_eqI_generator_eq[where A="?Iocn"]; simp)

next

  case False
  hence "einterval a b = {}" using einterval_empty by simp
  thus ?thesis by (metis sets.empty_sets space_empty_eq_bot space_restrict_space2)

qed

section \<open>Extending Nondecreasing Function\<close>

definition ext_mono_ei :: "ereal \<Rightarrow> ereal \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real" where
  "ext_mono_ei a b F x = (if ereal x \<le> a then (\<Sqinter>s \<in> einterval a b. F s) else
    if ereal x < b then F x else (\<Squnion>s \<in> einterval a b. F s))"
  \<comment> \<open>\<open>ei\<close> stands for "einterval".\<close>
  \<comment> \<open>In practice, \<open>ext_mono_ei a b\<close> trivially extends
       a nondecreasing function defined on \<open>einterval a b\<close>.\<close>

lemma ext_mono_ei_inf:
  fixes F :: "real \<Rightarrow> real" and a b :: ereal and x::real
  assumes "x \<le> a"
  shows "ext_mono_ei a b F x = (\<Sqinter>s \<in> einterval a b. F s)"
  unfolding ext_mono_ei_def using assms by simp

lemma ext_mono_ei_id:
  fixes F :: "real \<Rightarrow> real" and a b :: ereal and x::real
  assumes "x \<in> einterval a b"
  shows "ext_mono_ei a b F x = F x"
  unfolding ext_mono_ei_def using assms einterval_iff by force

lemma ext_mono_ei_sup:
  fixes F :: "real \<Rightarrow> real" and a b :: ereal and x::real
  assumes "a < b " "b \<le> x"
  shows "ext_mono_ei a b F x = (\<Squnion>s \<in> einterval a b. F s)"
  unfolding ext_mono_ei_def using assms by force

lemma deriv_ext_mono_ei_deriv:
  fixes F :: "real \<Rightarrow> real" and a b :: ereal and x::real
  assumes "x \<in> einterval a b"
  shows "deriv (ext_mono_ei a b F) x = deriv F x"
proof -
  have "\<forall>\<^sub>F s in nhds x. ext_mono_ei a b F s = F s"
    using ext_mono_ei_id assms
    by (smt (verit, ccfv_SIG) einterval_iff eventually_nhds open_einterval)
  thus "deriv (ext_mono_ei a b F) x = deriv F x" by (rule deriv_cong_ev; simp)
qed

lemma ext_mono_ei_mono:
  fixes F :: "real \<Rightarrow> real" and a b :: ereal
  assumes "mono F" "a < b"
  shows "mono (ext_mono_ei a b F)"
proof -
  let ?Iab = "einterval a b"
  have mono_b: "mono_on {z. ereal z < b} (ext_mono_ei a b F)"
  proof (rule mono_onI)
    fix x y :: real assume "x \<in> {z. ereal z < b}" "y \<in> {z. ereal z < b}" and xy: "x \<le> y"
    hence xb: "ereal x < b" and yb: "ereal y < b" by simp+
    show "(ext_mono_ei a b F) x \<le> (ext_mono_ei a b F) y"
    proof (cases \<open>a \<in> {ereal x ..< ereal y}\<close>)
      case True
      hence xa: "ereal x \<le> a" and ay: "a < ereal y" by force+
      hence "(ext_mono_ei a b F) x = (\<Sqinter>s\<in>?Iab. F s)" using ext_mono_ei_inf by simp
      also have "\<dots> \<le> F y"
      proof -
        have "\<And>z. z \<in> ?Iab \<Longrightarrow> F x \<le> F z"
          using assms xa einterval_iff ereal_less_ereal_Ex monoD by fastforce
        with bdd_below_def have "bdd_below (F`?Iab)" by force
        then show ?thesis using cINF_lower ay yb einterval_iff by metis
      qed
      also have "\<dots> = (ext_mono_ei a b F) y" using ay yb einterval_iff ext_mono_ei_id by simp
      finally show ?thesis .
    next
      case False
      from this consider (axy) "a < ereal x" | (xya) "ereal y \<le> a" by force
      thus ?thesis
      proof cases
        case axy
        hence "x \<in> ?Iab" "y \<in> ?Iab" using einterval_iff xb xy yb axy less_ereal_le by force+
        hence "(ext_mono_ei a b F) x = F x" "(ext_mono_ei a b F) y = F y"
          using ext_mono_ei_id by simp+
        thus ?thesis using xy assms monoD by simp
      next
        case xya
        moreover with xy have "ereal x \<le> a" using ereal_le_le by blast
        ultimately show ?thesis using ext_mono_ei_inf by simp
      qed
    qed
  qed
  show ?thesis
  proof (rule monoI)
    fix x y :: real assume xy: "x \<le> y"
    show "(ext_mono_ei a b F) x \<le> (ext_mono_ei a b F) y"
    proof (cases \<open>b \<in> {ereal x <.. ereal y}\<close>)
      case True
      hence xb: "ereal x < b" and bley: "b \<le> ereal y" by force+
      from assms xb obtain c where cIab: "c \<in> ?Iab" and "x < c"
        by (smt (verit, ccfv_SIG) einterval_iff einterval_nonempty
            less_ereal.simps(1) less_ereal_le)
      hence "(ext_mono_ei a b F) x \<le> (ext_mono_ei a b F) c"
        using mono_b xb by (simp add: einterval_iff mono_on_def)
      also have "\<dots> = F c" using cIab ext_mono_ei_id by blast
      also have "\<dots> \<le> (\<Squnion>s\<in>?Iab. F s)"
      proof -
        have "\<And>z. z \<in> ?Iab \<Longrightarrow> F z \<le> F y"
          using assms bley einterval_iff
          by (meson le_ereal_less linorder_not_le monoD order_trans_rules(20))
        with bdd_above_def have "bdd_above (F`?Iab)" by force
        thus ?thesis using cIab cSUP_upper by simp
      qed
      also have "\<dots> = (ext_mono_ei a b F) y" using ext_mono_ei_sup bley assms by presburger
      finally show ?thesis .
    next
      case False
      from this consider (bxy) "b \<le> ereal x" | (xyb) "ereal y < b" by force
      thus ?thesis
      proof cases
        case bxy
        hence "(ext_mono_ei a b F) x = (\<Squnion>s\<in>?Iab. F s)" using ext_mono_ei_sup assms by simp
        also have "\<dots> = (ext_mono_ei a b F) y"
          using ext_mono_ei_sup assms bxy xy le_ereal_le by presburger
        finally show ?thesis by simp
      next
        case xyb
        with mono_b xy show ?thesis by (simp add: ereal_less_le mono_on_def)
      qed
    qed
  qed
qed

lemma deriv_ext_mono_ei_nonneg: 
  fixes F :: "real \<Rightarrow> real" and a b :: ereal
  assumes "F differentiable_on (einterval a b)" "mono F" "a < b"
  shows "\<And>x. x \<in> einterval a b \<Longrightarrow> deriv (ext_mono_ei a b F) x \<ge> 0"
proof -
  let ?extF = "ext_mono_ei a b F"
  let ?Iab = "einterval a b"
  fix x assume xIab: "x \<in> ?Iab"
  have "mono_on ?Iab ?extF" using ext_mono_ei_mono monotone_on_subset assms by blast
  moreover with xIab have "(?extF has_real_derivative (deriv ?extF x)) (at x)"
    using deriv_ext_mono_ei_deriv apply (rewrite DERIV_cong_ev[of x x ?extF F _ "deriv F x"]; simp)
    using open_einterval eventually_nhds ext_mono_ei_id apply (smt (verit, ccfv_SIG))
    apply (rewrite DERIV_deriv_iff_field_differentiable)
    using assms differentiable_on_eq_field_differentiable_real
    by (metis at_within_open open_einterval)
  moreover have "x \<in> interior ?Iab" using open_einterval xIab by (simp add: interior_open)
  ultimately show "deriv ?extF x \<ge> 0" by (rule mono_on_imp_deriv_nonneg; simp)
qed

lemma ext_mono_ei_tendsto_at_right:
  fixes F :: "real \<Rightarrow> real" and a b :: ereal and ar::real
  assumes "mono F" "a < b" "a = ereal ar"
  shows "((ext_mono_ei a b F) \<longlongrightarrow> (\<Sqinter>s \<in> einterval a b. F s)) (at_right ar)"
proof -
  let ?extF = "ext_mono_ei a b F"
  let ?Iab = "einterval a b"
  obtain e where eIab: "e \<in> ?Iab" using assms einterval_nonempty by blast
  have "(?extF \<longlongrightarrow> (\<Sqinter>(?extF ` ({ar<..} \<inter> {..<e})))) (at ar within ({ar<..} \<inter> {..<e}))"
    using monoD ext_mono_ei_mono assms(1,2) by (intro Lim_right_bound[where K="?extF ar"]; smt)
  moreover have "at ar within ({ar<..} \<inter> {..<e}) = at_right ar"
    using at_within_Ioo_at_right eIab assms einterval_iff by force
  moreover have "\<Sqinter>(?extF`{ar<..<e}) = (\<Sqinter>s\<in>?Iab. F s)"
  proof -
    have "?extF`{ar<..<e} = F`{ar<..<e}"
      using assms eIab ext_mono_ei_id einterval_iff ereal_less_le by force
    moreover have "\<Sqinter>(F`{ar<..<e}) \<le> (\<Sqinter>s\<in>?Iab. F s)"
      apply (rule cINF_mono)
      using assms einterval_nonempty apply force
      apply (meson assms(1) bdd_below_Ioo bdd_below_image_mono)
      using assms monoD eIab einterval_iff
      by (smt (verit) einterval_eq_Icc einterval_nonempty ereal_less_le)
    moreover have "(\<Sqinter>s\<in>?Iab. F s) \<le> \<Sqinter>(F`{ar<..<e})"
      apply (rule cINF_superset_mono)
      using eIab assms apply (simp add: einterval_iff)
      apply (metis assms(1,3) bdd_below.I bdd_below_image_mono
          einterval_iff ereal_less_eq(3) less_le_not_le)
      using eIab assms
      apply (smt (verit) basic_trans_rules(19) einterval_eq(1) einterval_iff subsetI)
      by simp
    ultimately show ?thesis by simp
  qed
  ultimately show "(?extF \<longlongrightarrow> (\<Sqinter>s\<in>?Iab. F s)) (at_right ar)" by simp
qed

lemma ext_mono_ei_tendsto_at_left:
  fixes F :: "real \<Rightarrow> real" and a b :: ereal and br::real
  assumes "mono F" "a < b" "b = ereal br"
  shows "((ext_mono_ei a b F) \<longlongrightarrow> (\<Squnion>s \<in> einterval a b. F s)) (at_left br)"
proof -
  let ?extF = "ext_mono_ei a b F"
  let ?Iab = "einterval a b"
  obtain e where eIab: "e \<in> ?Iab" using assms einterval_nonempty by blast
  have "(?extF \<longlongrightarrow> (\<Squnion>(?extF ` ({..<br} \<inter> {e<..})))) (at br within ({..<br} \<inter> {e<..}))"
    using monoD ext_mono_ei_mono assms(1,2) by (intro Lim_left_bound[where K="?extF br"]; smt)
  moreover have "at br within ({..<br} \<inter> {e<..}) = at_left br"
    using at_within_Ioo_at_left eIab assms einterval_iff
    by (metis greaterThanLessThan_eq inf_commute less_ereal.simps(1))
  moreover have "\<Squnion>(?extF`{e<..<br}) = (\<Squnion>s\<in>?Iab. F s)"
  proof -
    have "?extF`{e<..<br} = F`{e<..<br}"
      using assms eIab ext_mono_ei_id einterval_iff
      by (smt (verit) basic_trans_rules(19) einterval_eq_Icc image_cong)
    moreover have "(\<Squnion>s\<in>?Iab. F s) \<le> \<Squnion>(F`{e<..<br})"
      apply (rule cSUP_mono)
      using assms einterval_nonempty apply force
       apply (metis assms(1) bdd_above.I2 bdd_above_Ioo cSup_upper monoD)
      using assms(1) monoD eIab assms einterval_iff
      by (smt (verit) einterval_eq(1) einterval_nonempty less_ereal.simps(1))
    moreover have "\<Squnion>(F`{e<..<br}) \<le> (\<Squnion>s\<in>?Iab. F s)"
      apply (rule cSUP_subset_mono)
      using eIab assms apply (simp add: einterval_iff)
        apply (metis assms(1,3) bdd_above.I bdd_above_image_mono
          einterval_iff ereal_less_eq(3) less_le_not_le)
      using eIab assms basic_trans_rules(19) einterval_iff apply fastforce
      by simp
    ultimately show ?thesis by simp
  qed
  ultimately show "(?extF \<longlongrightarrow> (\<Squnion>s\<in>?Iab. F s)) (at_left br)" by (simp add: inf_commute)
qed

lemma ext_mono_ei_continuous:
  fixes F :: "real \<Rightarrow> real" and a b :: ereal
  assumes "continuous_on (einterval a b) F" "mono F" "a < b"
  shows "continuous_on UNIV (ext_mono_ei a b F)"
proof (rule continuous_at_imp_continuous_on, safe)
  fix x
  let ?extF = "ext_mono_ei a b F"
  let ?Iab = "einterval a b"  consider (xa) "ereal x < a" | (a) "ereal x = a" | (axb) "x \<in> ?Iab" |
    (b) "ereal x = b" | (bx) "b < ereal x"
    using einterval_iff by force
  thus "isCont ?extF x"
  proof cases
    case xa
    have "continuous_on {z. ereal z < a} (\<lambda>_. (\<Sqinter>s\<in>?Iab. F s))" by (rule continuous_on_const)
    moreover have "\<And>z. ereal z < a \<Longrightarrow> ?extF z = (\<Sqinter>s\<in>?Iab. F s)" using ext_mono_ei_inf by simp
    ultimately have "continuous_on {z. ereal z < a} ?extF"
      using continuous_on_cong by (metis (no_types, lifting) mem_Collect_eq)
    thus ?thesis
      apply (rewrite in asm continuous_on_eq_continuous_at)
      using xa open_ereal_vimage[of "{..<a}"] unfolding vimage_def by simp_all
  next
    case a
    show ?thesis
    proof (rewrite continuous_at_split, safe)
      show "continuous (at_left x) ?extF"
      proof -
        have "?extF x = (\<Sqinter>s\<in>?Iab. F s)" using ext_mono_ei_inf a by simp
        moreover have "\<forall>\<^sub>F z in at_left x. ?extF z = (\<Sqinter>s\<in>?Iab. F s)"
          apply (rule eventually_at_leftI[of "x-1"]; simp)
          using ext_mono_ei_inf a by force
        moreover have "continuous (at_left x) (\<lambda>_. (\<Sqinter>s\<in>?Iab. F s))" by (rule continuous_const)
        ultimately show ?thesis
          by (rewrite continuous_at_within_cong[where g="\<lambda>_. (\<Sqinter>s\<in>?Iab. F s)"]; simp)
      qed
      show "continuous (at_right x) ?extF"
        using ext_mono_ei_tendsto_at_right ext_mono_ei_inf assms
        by (metis a continuous_within  less_eq_ereal_def)
    qed
  next
    case axb
    with continuous_on_eq_continuous_at ext_mono_ei_id show ?thesis
      by (metis assms(1) continuous_on_cong open_einterval)
  next
    case b
    show ?thesis
    proof (rewrite continuous_at_split, safe)
      from ext_mono_ei_tendsto_at_left assms show "continuous (at_left x) ?extF"
        by (metis ext_mono_ei_sup b continuous_within order.refl)
      show "continuous (at_right x) ?extF"
      proof -
        have "?extF x = (\<Squnion>s\<in>?Iab. F s)" using ext_mono_ei_sup assms b by simp
        moreover have "\<forall>\<^sub>F z in at_right x. ?extF z = (\<Squnion>s\<in>?Iab. F s)"
          apply (rule eventually_at_rightI[of x "x+1"]; simp)
          using ext_mono_ei_sup assms b by auto
        moreover have "continuous (at_right x) (\<lambda>_. (\<Squnion>s\<in>?Iab. F s))" by (rule continuous_const)
        ultimately show ?thesis
          by (rewrite continuous_at_within_cong[where g="\<lambda>_. (\<Squnion>s\<in>?Iab. F s)"]; simp)
      qed
    qed
  next
    case bx
    have "continuous_on {z. b < ereal z} (\<lambda>_. (\<Squnion>s\<in>?Iab. F s))" by (rule continuous_on_const)
    moreover have "\<And>z. b < ereal z \<Longrightarrow> ?extF z = (\<Squnion>s\<in>?Iab. F s)"
      using ext_mono_ei_sup assms  by simp
    ultimately have "continuous_on {z. b < ereal z} ?extF"
      using continuous_on_cong by (metis (no_types, lifting) mem_Collect_eq)
    thus ?thesis
      apply (rewrite in asm continuous_on_eq_continuous_at)
      using bx open_ereal_vimage[of "{b<..}"] unfolding vimage_def by simp_all
  qed
qed

lemma ext_mono_ei_piecewise_differentiable:
  fixes F :: "real \<Rightarrow> real" and a b :: ereal
  assumes "F differentiable_on (einterval a b)" "continuous_on (einterval a b) F" "mono F" "a < b"
  shows "ext_mono_ei a b F piecewise_differentiable_on UNIV"
proof -
  let ?extF = "ext_mono_ei a b F"
  let ?Iab = "einterval a b"
  have "\<exists>S :: real set. finite S \<and> (\<forall>x \<in> UNIV - S. ?extF differentiable at x)"
  proof -
    have "\<And>x. x \<in> UNIV - ereal -` {a,b} \<Longrightarrow> ?extF differentiable at x"
    proof -
      fix x assume "x \<in> UNIV - ereal -` {a,b}"
      from this consider (xa) "ereal x < a" | (axb) "x \<in> ?Iab" | (bx) "b < ereal x"
        using einterval_iff by fastforce
      thus "?extF differentiable at x"
      proof cases
        case xa
        have "(\<lambda>_. (\<Sqinter>s\<in>?Iab. F s)) differentiable (at x)" by (rule differentiable_const)
        moreover have "x \<in> ereal -` {..<a}" using xa by simp
        moreover have "open (ereal -` {..<a})" by (simp add: open_ereal_vimage)
        moreover have "\<And>z. z \<in> ereal -` {..<a} \<Longrightarrow> (\<Sqinter>s\<in>?Iab. F s) = ?extF z"
          using ext_mono_ei_inf by simp
        ultimately show ?thesis by (rule differentiable_transform_open)
      next
        case axb
        hence "?extF differentiable at x within ?Iab"
          using ext_mono_ei_id by (simp add: assms differentiable_onD differentiable_on_cong)
        thus ?thesis using at_within_open axb by fastforce
      next
        case bx
        have "(\<lambda>_. (\<Squnion>s\<in>?Iab. F s)) differentiable (at x)" by (rule differentiable_const)
        moreover have "x \<in> ereal -` {b<..}" using bx by simp
        moreover have "open (ereal -` {b<..})" by (simp add: open_ereal_vimage)
        moreover have "\<And>z. z \<in> ereal -` {b<..} \<Longrightarrow> (\<Squnion>s\<in>?Iab. F s) = ?extF z"
          using ext_mono_ei_sup assms by simp
        ultimately show ?thesis by (rule differentiable_transform_open)
      qed
    qed
    moreover have "finite (ereal -` {a,b})" by (rule finite_vimageI; simp)
    ultimately show ?thesis by blast
  qed
  with ext_mono_ei_continuous assms show ?thesis unfolding piecewise_differentiable_on_def by simp
qed

lemma ext_mono_ei_deriv_measurable:
  fixes F :: "real \<Rightarrow> real" and a b :: ereal
  assumes "F differentiable_on (einterval a b)" "mono F" "a < b"
  shows "deriv (ext_mono_ei a b F) \<in> borel_measurable lborel"
  apply (simp, rule piecewise_differentiable_on_deriv_measurable_real_UNIV)
  apply (rule ext_mono_ei_piecewise_differentiable)
  using ext_mono_ei_mono borel_measurable_mono differentiable_imp_continuous_on assms by simp_all

end
