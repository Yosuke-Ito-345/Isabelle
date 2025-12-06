theory Valuation
  imports Interest Annuity Life_Table
begin

declare[[show_types]]

section \<open>Auxiliary lemmas\<close>

context survival_model
begin

context
  fixes x::real
  assumes x_lt_psi[simp]: "x < $\<psi>"
begin

interpretation alivex_PS: prob_space "\<MM> \<downharpoonright> alive x"
  by (rule MM_PS.cond_prob_space_correct; simp add: alive_def)

interpretation distrTx_RD: real_distribution "distr (\<MM> \<downharpoonright> alive x) borel (T x)" by simp

lemma nn_integral_toTx_p:
  fixes \<BB> :: "real measure"
  assumes "sets \<BB> = sets borel" "sigma_finite_measure \<BB>" "g \<in> borel_measurable \<BB>"
  shows "(\<integral>\<^sup>+\<xi>. (\<integral>\<^sup>+t\<in>{..< T x \<xi>}. g t \<partial>\<BB>) \<partial>(\<MM> \<downharpoonright> alive x)) = \<integral>\<^sup>+t. (g t) * $p_{t&x} \<partial>\<BB>"
    (is "?LHS = ?RHS")
proof -
  have [simp]: "pair_sigma_finite \<BB> (\<MM> \<downharpoonright> alive x)"
    unfolding pair_sigma_finite_def using assms alivex_PS.sigma_finite_measure by blast
  have "?LHS = \<integral>\<^sup>+t. \<integral>\<^sup>+\<xi>. (g t) * (indicator {..< T x \<xi>} t) \<partial>(\<MM> \<downharpoonright> alive x) \<partial>\<BB>"
    using assms by (rewrite pair_sigma_finite.Fubini'; measurable; simp)
  also have "\<dots> = \<integral>\<^sup>+t. \<integral>\<^sup>+\<xi>. (g t) * (indicator {t<..} (T x \<xi>)) \<partial>(\<MM> \<downharpoonright> alive x) \<partial>\<BB>"
    apply (rule nn_integral_cong)+
    using indicator_simps by (metis greaterThan_iff lessThan_iff)
  also have "\<dots> = \<integral>\<^sup>+t. (g t) * \<integral>\<^sup>+\<xi>. indicator {t<..} (T x \<xi>) \<partial>(\<MM> \<downharpoonright> alive x) \<partial>\<BB>"
    by (rewrite nn_integral_cmult; simp)
  also have "\<dots> = ?RHS"
  proof -
    { fix t::real
      have [simp]: "{\<xi> \<in> space \<MM>. t < T x \<xi> \<and> 0 < T x \<xi>} \<in> alivex_PS.events"
      proof -
        have "{\<xi> \<in> space \<MM>. t < T x \<xi> \<and> 0 < T x \<xi>} = (alive x) \<inter> {\<xi> \<in> space \<MM>. t < T x \<xi>}"
          using alive_T unfolding Int_def by force
        moreover have "{\<xi> \<in> space \<MM>. t < T x \<xi>} \<in> MM_PS.events" by simp
        ultimately show ?thesis using MM_PS.sets_cond_prob_space by force
      qed
      have "(\<integral>\<^sup>+\<xi>. indicator {t<..} (T x \<xi>) \<partial>(\<MM> \<downharpoonright> alive x)) =
        nn_integral (\<MM> \<downharpoonright> alive x) (indicator {\<xi> \<in> space \<MM>. T x \<xi> > t \<and> T x \<xi> > 0})"
        unfolding indicator_def apply (rule nn_integral_cong)
        by simp (metis Int_iff MM_PS.space_cond_prob_space alive_event sets.Int_space_eq1)
      also have "\<dots> = emeasure (\<MM> \<downharpoonright> alive x) {\<xi> \<in> space \<MM>. T x \<xi> > t \<and> T x \<xi> > 0}"
        by (rewrite nn_integral_indicator; simp)
      also have "\<dots> = ennreal (\<P>(\<xi> in \<MM>. T x \<xi> > t \<bar> T x \<xi> > 0))"
        apply (rewrite alivex_PS.emeasure_eq_measure, rewrite alive_T)
        by (rewrite MM_PS.cond_prob_space_prob; simp)
      also have "\<dots> = ennreal ($p_{t&x})" by (rewrite p_PTx; simp)
      finally have "(\<integral>\<^sup>+\<xi>. indicator {t<..} (T x \<xi>) \<partial>(\<MM> \<downharpoonright> alive x)) = ennreal ($p_{t&x})" . }
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed

end

end

section \<open>Valuation\<close>

text \<open>
  In this theory, I describe various kinds of life insurance benefits and annuities in a uniform way.
  This allows us to generally define the actuarial present values of life contingencies.
\<close>

locale actuarial_model = interest + life_table

text \<open>
  In the following locale "val", I adopt some abbreviations for actuarial terms.
      (i) "ab" stands for "accumulated benefit".
     (ii) "tp" stands for "time of payment".
    (iii) "PV" stands for "present value".
     (iv) \<open>\<theta>\<close> represents the future lifetime of the insured.
      (v) \<open>t\<close> represents the time from the beginning of the life insurance contract.
     (vi) \<open>f\<close> represents the deferred period (possibly \<open>0\<close>).
  The precise meanings of "ab" and "tp" are as follows.
      (i) The value ab(\<open>\<theta>,t\<close>) represents the total amount of benefits
          that should be paid at or before the time \<open>t\<close>,
          on the assumption that the insured dies at the time \<open>\<theta>\<close>.
     (ii) The value tp(\<open>\<theta>,t\<close>) represents the actual time
          when the benefit is paid whose obligation is incurred at the time \<open>t\<close>,
          on the assumption that the insured dies at the time \<open>\<theta>\<close>.
\<close>

locale val = actuarial_model +
  \<comment> \<open>"val" stands for "valuation".\<close>
  fixes f::real and ab :: "real \<Rightarrow> real \<Rightarrow> real" and tp :: "real \<Rightarrow> real \<Rightarrow> real"
  assumes f_nonneg[simp]: "f \<ge> 0" and
    ab_f_0[simp]: "\<And>\<theta> t. t < f \<Longrightarrow> ab \<theta> t = 0" and
    ab_right_continuous[simp]: "\<And>\<theta> t. continuous (at_right t) (ab \<theta>)" and
    ab_mono[simp]: "\<And>\<theta>. mono (ab \<theta>)" and
    tp_measurable[measurable]: "\<And>\<theta>. (tp \<theta>) \<in> borel_measurable borel" and
    PV_measurable[measurable]: "(\<lambda>\<theta>. \<integral>\<^sup>+t. $v.^(tp \<theta> t) \<partial>(IM (ab \<theta>))) \<in> borel_measurable borel"
begin

definition APV :: "real \<Rightarrow> real" where
  "APV x \<equiv> \<integral>\<xi>. \<integral>t. $v.^(tp (T x \<xi>) t) \<partial>(IM (ab (T x \<xi>))) \<partial>(\<MM> \<downharpoonright> alive x)"
  \<comment> \<open>actuarial present value of the life-contingent cash flows at age \<open>x\<close>\<close>
  \<comment> \<open>When the integral diverges, this definition is interpreted as meaningless.\<close>

definition ennAPV :: "real \<Rightarrow> ennreal" where
  "ennAPV x \<equiv> \<integral>\<^sup>+\<xi>. \<integral>\<^sup>+t. $v.^(tp (T x \<xi>) t) \<partial>(IM (ab (T x \<xi>))) \<partial>(\<MM> \<downharpoonright> alive x)"

lemma ab_measurable[measurable]: "\<And>\<theta>. (ab \<theta>) \<in> borel_measurable borel"
  by (rule borel_measurable_mono) simp

lemma ab_constant_on_f:
  fixes \<theta>::real
  shows "(ab \<theta>) constant_on {..<f}"
  using ab_f_0 by (simp add: constant_on_def)

lemma PV_measurable'[measurable]: "(\<lambda>\<theta>. \<integral>t. $v.^(tp \<theta> t) \<partial>(IM (ab \<theta>))) \<in> borel_measurable borel"
proof -
  have "\<And>\<theta>. (\<integral>t. $v.^(tp \<theta> t) \<partial>(IM (ab \<theta>))) = enn2real (\<integral>\<^sup>+t. ennreal ($v.^(tp \<theta> t)) \<partial>(IM (ab \<theta>)))"
  proof -
    fix \<theta>::real
    have neg0: "(\<integral>\<^sup>+t. ennreal (-($v.^(tp \<theta> t))) \<partial>(IM (ab \<theta>))) = 0"
      apply (rule nn_integral_zero')
      apply (rule AE_I2, simp)
      by (rule ennreal_neg) simp
    show "(\<integral>t. $v.^(tp \<theta> t) \<partial>(IM (ab \<theta>))) = enn2real (\<integral>\<^sup>+t. ennreal ($v.^(tp \<theta> t)) \<partial>(IM (ab \<theta>)))"
    proof (cases \<open>(\<integral>\<^sup>+t. ennreal ($v.^(tp \<theta> t)) \<partial>(IM (ab \<theta>))) = \<infinity>\<close>)
      case True
      hence "\<not> integrable (IM (ab \<theta>)) (\<lambda>t. $v.^(tp \<theta> t))" using real_integrable_def by force
      hence "(\<integral>t. $v.^(tp \<theta> t) \<partial>(IM (ab \<theta>))) = 0" using not_integrable_integral_eq by force
      thus ?thesis using True by simp
    next
      case False
      moreover have "(\<lambda>t. $v.^(tp \<theta> t)) \<in> borel_measurable (IM (ab \<theta>))"
        using tp_measurable by measurable
      ultimately have "integrable (IM (ab \<theta>)) (\<lambda>t. $v.^(tp \<theta> t))"
        using real_integrable_def neg0 by force
      thus ?thesis using real_lebesgue_integral_def neg0 by force
    qed
  qed
  thus ?thesis using borel_measurable_enn2real PV_measurable by simp
qed

lemma APV_nonneg:
  fixes x::real
  shows "APV x \<ge> 0"
  unfolding APV_def by (rule Bochner_Integration.integral_nonneg)+ simp

lemma ennAPV_APV:
  fixes x::real
  assumes "\<And>\<theta>. \<theta> > 0 \<Longrightarrow> (\<integral>\<^sup>+t. $v.^(tp \<theta> t) \<partial>(IM (ab \<theta>))) < \<infinity>" "ennAPV x < \<infinity>"
  shows "ennAPV x = ennreal (APV x)"
proof -
  have "ennAPV x = \<integral>\<^sup>+\<xi>. ennreal (\<integral>t. $v.^(tp (T x \<xi>) t) \<partial>(IM (ab (T x \<xi>)))) \<partial>(\<MM> \<downharpoonright> alive x)"
    unfolding ennAPV_def apply(rule nn_integral_cong)
    apply (rewrite nn_integral_eq_integral; simp?)
    using assms(1) by (intro integrableI_bounded; simp)
  also have "\<dots> = ennreal (APV x)"
    unfolding APV_def apply (rewrite nn_integral_eq_integral; simp?)
    using calculation assms(2) by (intro integrableI_bounded; simp)
  finally show ?thesis. 
qed

end

subsection \<open>Term Life\<close>

locale val_term_life = val +
  fixes n::real
  assumes n_nonneg[simp]: "n \<ge> 0" and
    ab_eq_fn: "\<And>\<theta> t. t \<ge> f + n \<Longrightarrow> ab \<theta> t = ab \<theta> (f + n)"
begin

lemma ab_constant_on_fn:
  fixes \<theta> t :: real
  shows "(ab \<theta>) constant_on {f+n..}"
  using ab_eq_fn by (meson atLeast_iff constant_on_def)

end

subsection \<open>Life Annuity\<close>

locale val_life_ann = actuarial_model + annuity
begin

definition ab :: "real \<Rightarrow> real \<Rightarrow> real" where
  "ab \<theta> t \<equiv> (if t < \<theta> then abg t else Lim (at_left \<theta>) abg)"

definition tp :: "real \<Rightarrow> real \<Rightarrow> real" where "tp \<theta> t \<equiv> t"

lemma ab_eq_abg:
  fixes \<theta> t :: real
  assumes "t < \<theta>"
  shows "ab \<theta> t = abg t"
  using ab_def assms by simp

lemma ab_eq_Lim_abg:
  fixes \<theta> t :: real
  assumes "\<theta> \<le> t"
  shows "ab \<theta> t = Lim (at_left \<theta>) abg"
  using assms ab_def by simp

lemma ab_constant_on_th:
  fixes \<theta>:: real
  shows "(ab \<theta>) constant_on {\<theta>..}"
  unfolding constant_on_def using ab_eq_Lim_abg by simp

lemma ab_right_continuous[simp]:
  fixes \<theta> t :: real
  shows "continuous (at_right t) (ab \<theta>)"
proof (cases \<open>t < \<theta>\<close>)
  case True
  thus ?thesis
    apply (rewrite continuous_at_within_cong[where g=abg])
    using eventually_at_rightI[of _ \<theta>] by (simp_all add: ab_eq_abg)
next
  case False
  thus ?thesis
    apply (rewrite continuous_at_within_cong[where g="\<lambda>_. Lim (at_left \<theta>) abg"])
    using eventually_at_rightI[of _ "t+1"] by (simp_all add: ab_eq_Lim_abg)
qed

lemma abg_tendsto_Sup_th:
  fixes \<theta>::real
  shows "(abg \<longlongrightarrow> Sup (abg ` {..<\<theta>})) (at_left \<theta>)"
  apply (rule Lim_left_bound[where I=UNIV and K="abg \<theta>", simplified])
  using abg_mono monoD order_less_imp_le by blast+

corollary Sup_abg_ab:
  fixes \<theta>::real
  shows "Sup (abg ` {..<\<theta>}) = ab \<theta> \<theta>"
  using abg_tendsto_Sup_th tendsto_Lim ab_eq_Lim_abg[of \<theta> \<theta>]
  by (smt (verit, best) trivial_limit_at_left_real)

corollary isCont_ab_th:
  fixes \<theta>::real
  shows "isCont (ab \<theta>) \<theta>"
  apply (rewrite continuous_at_split, simp, rewrite continuous_within)
  using ab_eq_abg abg_tendsto_Sup_th Sup_abg_ab by (metis Lim_cong_within lessThan_iff)

lemma ab_f_0[simp]:
  fixes \<theta> t :: real
  assumes "t < f"
  shows "ab \<theta> t = 0"
proof (cases \<open>t < \<theta>\<close>)
  case True
  thus ?thesis using ab_eq_abg assms by simp
next
  case False
  hence "\<theta> < f" using assms by simp
  hence "\<And>s. s < \<theta> \<Longrightarrow> abg s = 0" by simp
  hence "Sup (abg ` {..<\<theta>}) = 0" by (rewrite SUP_cong[where B="{..<\<theta>}" and D="\<lambda>_. 0"]; simp)
  hence "ab \<theta> \<theta> = 0" using Sup_abg_ab by simp
  thus ?thesis using False ab_eq_Lim_abg by simp
qed

lemma ab_constant_on_f:
  fixes \<theta>::real
  shows "(ab \<theta>) constant_on {..<f}"
  using ab_f_0 by (simp add: constant_on_def)

lemma ab_mono[simp]:
  fixes \<theta>::real
  shows "mono (ab \<theta>)"
proof
  fix s t ::real assume st: "s \<le> t"
  from this consider (tth) "t < \<theta>" | (stht) "s < \<theta> \<and> \<theta> \<le> t" | (ths) "\<theta> \<le> s" by force
  thus "ab \<theta> s \<le> ab \<theta> t"
  proof cases
    case tth
    then show ?thesis using ab_eq_abg abg_mono st monoD by smt
  next
    case stht
    hence "ab \<theta> s = abg s" using ab_eq_abg by simp
    also have "abg s \<le> ab \<theta> \<theta>"
      by (rewrite Sup_abg_ab[THEN sym], simp add: bdd_above_image_mono cSUP_upper stht)
    also have "\<dots> = ab \<theta> t" using ab_eq_Lim_abg stht by simp
    finally show ?thesis .
  next
    case ths
    then show ?thesis using ab_eq_Lim_abg st by simp
  qed
qed

lemma tp_measurable[measurable]:
  fixes \<theta>::real
  shows "tp \<theta> \<in> borel_measurable borel"
  unfolding tp_def by simp

lemma PV_abg:
  fixes \<theta>::real
  shows "(\<integral>\<^sup>+t. $v.^(tp \<theta> t) \<partial>(IM (ab \<theta>))) = (\<integral>\<^sup>+t\<in>{f..<\<theta>}. $v.^t \<partial>(IM abg))"
proof -
  have "ab \<theta> constant_on {\<theta><..}"
    using ab_constant_on_th by (meson Ioi_le_Ico constant_on_subset)
  hence "(\<integral>\<^sup>+t. ennreal ($v.^(tp \<theta> t)) \<partial>(IM (ab \<theta>))) = (\<integral>\<^sup>+t\<in>{f..<\<theta>}. ennreal ($v.^t) \<partial>(IM (ab \<theta>)))"
    unfolding tp_def using isCont_ab_th ab_constant_on_f
    by (rewrite nn_integral_interval_measure_Ico; simp)
  also have "\<dots> = (\<integral>\<^sup>+t\<in>{f..<\<theta>}. ennreal ($v.^t) \<partial>(IM abg))"
  proof (cases \<open>f < \<theta>\<close>)
    case True
    have "Lim (at_left f) (ab \<theta>) = Lim (at_left f) abg"
      by (rule Lim_cong, rule eventually_at_leftI[of "f-1"]; simp)
    with True show ?thesis
      by (rewrite Ico_nn_integral_interval_measure_cong;
          simp add: fun_diff_def ab_eq_abg constant_on_def)
  next
    case False
    thus ?thesis by (rewrite Ico_nn_integral_interval_measure_cong; simp add: constant_on_def)
  qed
  finally show ?thesis .
qed

lemma PV_measurable[measurable]: "(\<lambda>\<theta>. \<integral>\<^sup>+t. $v.^(tp \<theta> t) \<partial>(IM (ab \<theta>))) \<in> borel_measurable borel"
proof -
  have "Measurable.pred (borel \<Otimes>\<^sub>M borel) (\<lambda>(\<theta>,t). t \<in> {f..<\<theta>})" by simp
  hence "(\<lambda>(\<theta>,t). $v.^t * indicator {f..<\<theta>} t) \<in> borel_measurable (lborel \<Otimes>\<^sub>M IM abg)"
    by measurable
  moreover have "sigma_finite_measure (IM abg)"
    by (rule sigma_finite_interval_measure; simp add: monoD)
  ultimately have "(\<lambda>\<theta>. \<integral>\<^sup>+t. $v.^t * indicator {f..<\<theta>} t \<partial>(IM abg)) \<in> borel_measurable borel"
    using sigma_finite_measure.borel_measurable_nn_integral_fst
      [of _ "\<lambda>(\<theta>,t). $v.^t * indicator {f..<\<theta>} t"]
    by simp
  moreover have "(\<lambda>\<theta>. \<integral>\<^sup>+t. $v.^(tp \<theta> t) \<partial>(IM (ab \<theta>))) =
    (\<lambda>\<theta>. (\<integral>\<^sup>+t. $v.^t * indicator {f..<\<theta>} t \<partial>(IM abg)))"
    using PV_abg by (simp add: nn_integral_set_ennreal)
  ultimately show ?thesis by simp
qed


end












(* Trying to replace \<open>Living Benefit\<close> to \<open>Life Annuity\<close> *)
subsection \<open>Living Benefit\<close>

(* TODO : Modify to include the locale "annuity". *)
locale val_living = actuarial_model +
  fixes f::real and abl :: "real \<Rightarrow> real" and tpl :: "real \<Rightarrow> real"
  assumes f_nonneg[simp]: "f \<ge> 0" and
    abl_f_0[simp]: "\<And>t. t < f \<Longrightarrow> abl t = 0" and
    abl_right_continuous[simp]: "\<And>t. continuous (at_right t) abl" and
    abl_mono[simp]: "mono abl" and
    tpl_measurable[measurable]: "tpl \<in> borel_measurable borel"
begin

lemma abl_measurable[measurable]: "abl \<in> borel_measurable borel"
  using abl_mono borel_measurable_mono by simp

definition ab :: "real \<Rightarrow> real \<Rightarrow> real" where
  "ab \<theta> t \<equiv> (if t < \<theta> then abl t else Lim (at_left \<theta>) abl)"

definition tp :: "real \<Rightarrow> real \<Rightarrow> real" where "tp \<theta> t \<equiv> tpl t"

lemma ab_eq_abl:
  fixes \<theta> t :: real
  assumes "t < \<theta>"
  shows "ab \<theta> t = abl t"
  using ab_def assms by simp

lemma ab_eq_Lim_abl:
  fixes \<theta> t :: real
  assumes "\<theta> \<le> t"
  shows "ab \<theta> t = Lim (at_left \<theta>) abl"
  using assms ab_def by simp

lemma ab_constant_on_th:
  fixes \<theta>:: real
  shows "(ab \<theta>) constant_on {\<theta>..}"
  unfolding constant_on_def using ab_eq_Lim_abl by simp

lemma ab_right_continuous[simp]:
  fixes \<theta> t :: real
  shows "continuous (at_right t) (ab \<theta>)"
proof (cases \<open>t < \<theta>\<close>)
  case True
  thus ?thesis
    apply (rewrite continuous_at_within_cong[where g=abl])
    using eventually_at_rightI[of _ \<theta>] by (simp_all add: ab_eq_abl)
next
  case False
  thus ?thesis
    apply (rewrite continuous_at_within_cong[where g="\<lambda>_. Lim (at_left \<theta>) abl"])
    using eventually_at_rightI[of _ "t+1"] by (simp_all add: ab_eq_Lim_abl)
qed

lemma abl_tendsto_Sup_th:
  fixes \<theta>::real
  shows "(abl \<longlongrightarrow> Sup (abl ` {..<\<theta>})) (at_left \<theta>)"
  apply (rule Lim_left_bound[where I=UNIV and K="abl \<theta>", simplified])
  using abl_mono monoD order_less_imp_le by blast+

corollary Sup_abl_ab:
  fixes \<theta>::real
  shows "Sup (abl ` {..<\<theta>}) = ab \<theta> \<theta>"
  using abl_tendsto_Sup_th tendsto_Lim ab_eq_Lim_abl[of \<theta> \<theta>]
  by (smt (verit, best) trivial_limit_at_left_real)

corollary isCont_ab_th:
  fixes \<theta>::real
  shows "isCont (ab \<theta>) \<theta>"
  apply (rewrite continuous_at_split, simp, rewrite continuous_within)
  using ab_eq_abl abl_tendsto_Sup_th Sup_abl_ab by (metis Lim_cong_within lessThan_iff)

lemma ab_f_0[simp]:
  fixes \<theta> t :: real
  assumes "t < f"
  shows "ab \<theta> t = 0"
proof (cases \<open>t < \<theta>\<close>)
  case True
  thus ?thesis using ab_eq_abl assms by simp
next
  case False
  hence "\<theta> < f" using assms by simp
  hence "\<And>s. s < \<theta> \<Longrightarrow> abl s = 0" by simp
  hence "Sup (abl ` {..<\<theta>}) = 0" by (rewrite SUP_cong[where B="{..<\<theta>}" and D="\<lambda>_. 0"]; simp)
  hence "ab \<theta> \<theta> = 0" using Sup_abl_ab by simp
  thus ?thesis using False ab_eq_Lim_abl by simp
qed

lemma ab_constant_on_f:
  fixes \<theta>::real
  shows "(ab \<theta>) constant_on {..<f}"
  using ab_f_0 by (simp add: constant_on_def)

lemma ab_mono[simp]:
  fixes \<theta>::real
  shows "mono (ab \<theta>)"
proof
  fix s t ::real assume st: "s \<le> t"
  from this consider (tth) "t < \<theta>" | (stht) "s < \<theta> \<and> \<theta> \<le> t" | (ths) "\<theta> \<le> s" by force
  thus "ab \<theta> s \<le> ab \<theta> t"
  proof cases
    case tth
    then show ?thesis using ab_eq_abl abl_mono st monoD by smt
  next
    case stht
    hence "ab \<theta> s = abl s" using ab_eq_abl by simp
    also have "abl s \<le> ab \<theta> \<theta>"
      by (rewrite Sup_abl_ab[THEN sym], simp add: bdd_above_image_mono cSUP_upper stht)
    also have "\<dots> = ab \<theta> t" using ab_eq_Lim_abl stht by simp
    finally show ?thesis .
  next
    case ths
    then show ?thesis using ab_eq_Lim_abl st by simp
  qed
qed

lemma tp_measurable[measurable]:
  fixes \<theta>::real
  shows "tp \<theta> \<in> borel_measurable borel"
  using tp_def tpl_measurable by presburger

lemma PV_abl_tpl:
  fixes \<theta>::real
  shows "(\<integral>\<^sup>+t. $v.^(tp \<theta> t) \<partial>(IM (ab \<theta>))) = (\<integral>\<^sup>+t\<in>{f..<\<theta>}. $v.^(tpl t) \<partial>(IM abl))"
proof -
  have "(\<integral>\<^sup>+t. ennreal ($v.^(tp \<theta> t)) \<partial>(IM (ab \<theta>))) =
      (\<integral>\<^sup>+t\<in>{f..<\<theta>}. ennreal ($v.^(tpl t)) \<partial>(IM (ab \<theta>)))"
    using isCont_ab_th apply (rewrite tp_def, rewrite nn_integral_interval_measure_Ico; simp?)
    using ab_constant_on_f apply simp
    using ab_constant_on_th by (meson Ioi_le_Ico constant_on_subset)
  also have "\<dots> = (\<integral>\<^sup>+t\<in>{f..<\<theta>}. ennreal ($v.^(tpl t)) \<partial>(IM abl))"
  proof (cases \<open>f < \<theta>\<close>)
    case True
    then show ?thesis
      apply (rewrite Ico_nn_integral_interval_measure_cong;
          simp add: fun_diff_def ab_eq_abl constant_on_def)
      by (rule Lim_cong, rule eventually_at_leftI[of "f-1"]; simp)
  next
    case False
    thus ?thesis by (rewrite Ico_nn_integral_interval_measure_cong; simp add: constant_on_def)
  qed
  finally show ?thesis .
qed

lemma PV_measurable[measurable]: "(\<lambda>\<theta>. \<integral>\<^sup>+t. $v.^(tp \<theta> t) \<partial>(IM (ab \<theta>))) \<in> borel_measurable borel"
proof -
  have "(\<lambda>\<theta>. \<integral>\<^sup>+t. ennreal ($v.^(tp \<theta> t)) \<partial>(IM (ab \<theta>))) =
    (\<lambda>\<theta>. (\<integral>\<^sup>+t. ennreal ($v.^(tpl t) * indicator {f..<\<theta>} t) \<partial>(IM abl)))"
    using PV_abl_tpl by (simp add: nn_integral_set_ennreal)
  moreover have
    "(\<lambda>\<theta>. \<integral>\<^sup>+t. ennreal ($v.^(tpl t) * indicator {f..<\<theta>} t) \<partial>(IM abl)) \<in> borel_measurable borel"
    using sigma_finite_measure.borel_measurable_nn_integral_fst
      [of _ "\<lambda>(\<theta>,t). ennreal ($v.^(tpl t) * indicator {f..<\<theta>} t)", simplified]
    apply (measurable, simp add: monoD sigma_finite_interval_measure)
    by measurable simp
  ultimately show ?thesis by simp
qed

end

sublocale val_living \<subseteq> val i l f ab tp
  by (standard; simp)

context val_living
begin

lemma ennAPV_nn_integral_interval_measure_abl:
  assumes "x < $\<psi>"
  shows "ennAPV x = (\<integral>\<^sup>+t\<in>{f..}. $v.^(tpl t) * $p_{t&x} \<partial>(IM abl))"
    (is "?LHS = ?RHS")
proof -
  { fix \<xi> assume "\<xi> \<in> space (\<MM> \<downharpoonright> alive x)"
    have "(\<integral>\<^sup>+t. ennreal ($v.^(tp (T x \<xi>) t)) \<partial>(IM (ab (T x \<xi>)))) = 
      (\<integral>\<^sup>+t\<in>{..< T x \<xi>}. ennreal ($v.^(tp (T x \<xi>) t)) \<partial>(IM (ab (T x \<xi>))))"
      apply (rewrite nn_integral_interval_measure_Iio[where s="T x \<xi>"], simp_all add: isCont_ab_th)
      using ab_constant_on_th by (meson Ioi_le_Ico constant_on_subset)
    also have "\<dots> = (\<integral>\<^sup>+t\<in>{..< T x \<xi>}. ennreal ($v.^(tp (T x \<xi>) t)) \<partial>(IM abl))"
      by (rule Iio_nn_integral_interval_measure_cong;
          simp add: fun_diff_def ab_eq_abl constant_on_def)
    also have "\<dots> = (\<integral>\<^sup>+t\<in>{..< T x \<xi>}. ennreal ($v.^(tpl t)) \<partial>(IM abl))" using tp_def by simp
    finally have
      "(\<integral>\<^sup>+t. ennreal ($v.^(tp (T x \<xi>) t)) \<partial>(IM (ab (T x \<xi>)))) =
        (\<integral>\<^sup>+t\<in>{..< T x \<xi>}. ennreal ($v.^(tpl t)) \<partial>(IM abl))" . }
  hence "?LHS = \<integral>\<^sup>+\<xi>. (\<integral>\<^sup>+t\<in>{..< T x \<xi>}. ennreal ($v.^(tpl t)) \<partial>(IM abl)) \<partial>(\<MM> \<downharpoonright> alive x)"
    unfolding ennAPV_def by (meson nn_integral_cong)
  also have "\<dots> = (\<integral>\<^sup>+t. $v.^(tpl t) * $p_{t&x} \<partial>(interval_measure abl))"
    using assms
    by (rewrite nn_integral_toTx_p; simp add: sigma_finite_interval_measure monoD ennreal_mult')
  also have "\<dots> = ?RHS"
    by (rewrite nn_integral_interval_measure_Ici; simp add: fun_diff_def constant_on_def assms)
  finally show ?thesis .
qed

end

subsection \<open>Term Life with Living Benefit\<close>

locale val_term_life_living = val_living +
  fixes n::real
  assumes n_nonneg[simp]: "n \<ge> 0" and
    abl_eq_fn: "\<And>t. t \<ge> f + n \<Longrightarrow> abl t = abl (f + n)"
begin 

lemma ab_eq_fn:
  fixes \<theta> t :: real
  assumes "t \<ge> f + n"
  shows "ab \<theta> t = ab \<theta> (f + n)"
proof (cases \<open>f + n < \<theta>\<close>)
  case fnth: True
  thus ?thesis
  proof (cases \<open>t < \<theta>\<close>)
    case True
    hence "ab \<theta> t = abl t" using ab_eq_abl by simp
    also have "\<dots> = abl (f + n)" using abl_eq_fn assms by blast
    also have "\<dots> = ab \<theta> (f + n)" using fnth ab_eq_abl by simp
    finally show ?thesis .
  next
    case False
    hence "ab \<theta> t = Lim (at_left \<theta>) abl" using ab_eq_Lim_abl by simp
    also have "\<dots> = abl (f + n)"
    proof -
      have "\<And>s. s \<noteq> \<theta> \<Longrightarrow> s \<in> {f+n<..<\<theta>} \<Longrightarrow> abl s = abl (f + n)" by (rule abl_eq_fn) simp
      hence "(abl \<longlongrightarrow> abl (f + n)) (at_left \<theta>)"
        apply (rewrite at_within_Ioo_at_left[THEN sym, of "f+n"], simp add: fnth)
        by (rewrite Lim_cong_within[where g="\<lambda>_. abl (f+n)"]; simp) simp+
      thus ?thesis using tendsto_Lim by force
    qed
    also have "\<dots> = ab \<theta> (f + n)" using fnth ab_eq_abl by simp
    finally show ?thesis .
  qed
next
  case False
  thus ?thesis using ab_eq_Lim_abl assms by force
qed

end

sublocale val_term_life_living \<subseteq> val_term_life i l f ab tp n
  apply (standard, simp)
  using ab_eq_fn by blast

context val_term_life_living
begin

corollary abl_constant_on_fn: "abl constant_on {f+n..}"
  using abl_eq_fn by (meson atLeast_iff constant_on_def)

lemma ennAPV_term_nn_integral_interval_measure_abl:
  assumes "x < $\<psi>"
  shows "ennAPV x = (\<integral>\<^sup>+t\<in>{f..f+n}. $v.^(tpl t) * $p_{t&x} \<partial>(IM abl))"
proof -
  have "ennAPV x = (\<integral>\<^sup>+t. ennreal ($v.^(tpl t) * $p_{t&x}) * indicator {f..} t \<partial>(IM abl))"
    using ennAPV_nn_integral_interval_measure_abl assms by simp
  also have "\<dots> = (\<integral>\<^sup>+t\<in>{..f+n}. ennreal ($v.^(tpl t) * $p_{t&x}) * indicator {f..} t \<partial>(IM abl))"
    using assms apply (rewrite nn_integral_interval_measure_Iic; simp)
    using abl_constant_on_fn by (meson Ioi_le_Ico constant_on_subset)
  also have "\<dots> = (\<integral>\<^sup>+t\<in>{f..f+n}. ennreal ($v.^(tpl t) * $p_{t&x}) \<partial>(IM abl))"
    apply (rule nn_integral_cong)
    by (metis arithmetic_simps(79) atLeastAtMost_iff atLeast_iff
        atMost_iff ennreal_mult_right_cong indicator_simps(1,2))
  finally show ?thesis .
qed

end

subsection \<open>Deferred Continuous Whole Life Annuity\<close>

locale val_defer_cont_whole_life_ann = actuarial_model +
  fixes f::real
  assumes f_nonneg[simp]: "f \<ge> 0"
begin

definition abl :: "real \<Rightarrow> real" where "abl t \<equiv> max (t - f) 0"

definition tpl :: "real \<Rightarrow> real" where "tpl t = t"

lemma abl_f_0[simp]:
  fixes t::real
  assumes "t < f"
  shows "abl t = 0"
  unfolding abl_def using assms by simp

lemma abl_continuous[simp]:
  fixes t::real
  shows "isCont abl t"
  unfolding abl_def by (simp add: continuous_max)

corollary
  fixes t::real
  shows abl_right_continuous[simp]: "continuous (at_right t) abl" and
    abl_left_continuous[simp]: "continuous (at_left t) abl"
  by (simp add: continuous_at_imp_continuous_within)+

lemma abl_mono[simp]: "mono abl"
  unfolding abl_def by (simp add: monoI)

lemma tpl_measurable[measurable]: "tpl \<in> borel_measurable borel"
  unfolding tpl_def by simp

end

sublocale val_defer_cont_whole_life_ann \<subseteq> val_living i l f abl tpl
  by (standard; simp)

context val_defer_cont_whole_life_ann
begin

lemma DERIV_abl:
  fixes t::real
  assumes "f < t"
  shows "DERIV abl t :> 1"
proof -
  have "DERIV (\<lambda>s. s - f) t :> 1 - 0" by (intro derivative_intros)
  thus "DERIV abl t :> 1"
    apply (rewrite DERIV_cong_ev; simp)
    apply (rewrite eventually_nhds_metric)
    by (rule exI[of _ "t-f"], auto simp add: assms abl_def dist_real_def)
qed

corollary abl_differentiable_on_f: "abl differentiable_on {f<..}"
  by (meson DERIV_abl differentiable_at_withinI differentiable_on_def
      greaterThan_iff real_differentiable_def)

corollary deriv_abl:
  fixes t::real
  assumes "f < t"
  shows "deriv abl t = 1"
  using assms DERIV_abl DERIV_imp_deriv by blast

lemma set_nn_integral_interval_measure_abl:
  fixes g :: "real \<Rightarrow> real" and A :: "real set"
  assumes "g \<in> borel_measurable borel" and
    A_borel: "A \<in> sets borel" "A \<subseteq> {f..}"
  shows "(\<integral>\<^sup>+t\<in>A. g t \<partial>(IM abl)) = (\<integral>\<^sup>+t\<in>A. g t \<partial>lborel)"
proof -

  wlog A_f: "A \<subseteq> {f<..}" generalizing A keeping A_borel
  proof -
    from assms negation have fA: "f \<in> A" using dual_order.strict_iff_order by auto
    hence "(\<integral>\<^sup>+t\<in>A. g t \<partial>(IM abl)) = (\<integral>\<^sup>+t\<in>{f}. g t \<partial>(IM abl)) + (\<integral>\<^sup>+t\<in>A-{f}. g t \<partial>(IM abl))"
      using assms by (rewrite nn_integral_disjoint_pair[THEN sym]; simp add: insert_absorb)
    also have "\<dots> = (\<integral>\<^sup>+t\<in>A-{f}. g t \<partial>lborel)"
    proof -
      have "(\<integral>\<^sup>+t\<in>{f}. g t \<partial>(IM abl)) = 0" using interval_measure_singleton_continuous by simp
      moreover have "(\<integral>\<^sup>+t\<in>A-{f}. g t \<partial>(IM abl)) = (\<integral>\<^sup>+t\<in>A-{f}. g t \<partial>lborel)"
        using assms A_borel by (intro hypothesis; force)
      ultimately show ?thesis by simp
    qed
    also have "\<dots> = (\<integral>\<^sup>+t\<in>{f}. g t \<partial>lborel) + (\<integral>\<^sup>+t\<in>A-{f}. g t \<partial>lborel)" by simp
    also have "\<dots> = (\<integral>\<^sup>+t\<in>A. g t \<partial>lborel)"
      using assms fA by (rewrite nn_integral_disjoint_pair[THEN sym]; simp add: insert_absorb)
    finally show ?thesis .
  qed

  thus ?thesis
  proof -
    have "(\<integral>\<^sup>+t\<in>A. g t \<partial>(IM abl)) = (\<integral>\<^sup>+t\<in>A. ennreal (g t) * ennreal (deriv abl t) \<partial>lborel)"
      using assms A_borel A_f abl_differentiable_on_f deriv_abl
      by (rewrite set_nn_integral_interval_measure_deriv[of abl f \<infinity>]; simp)
    also have "\<dots> = (\<integral>\<^sup>+t\<in>A. g t \<partial>lborel)"
      apply (intro set_nn_integral_cong)
      using deriv_abl A_f by force+
    finally show ?thesis .
  qed
qed

lemma
  fixes x::real
  assumes "i > 0" "x < $\<psi>"
  shows APV_set_integrable: "set_integrable lborel {f..} (\<lambda>t. $v.^t * $p_{t&x})" and
    APV_calc: "APV x = (LBINT t:{f..}. $v.^t * $p_{t&x})"
proof -

  text \<open>Proof of "APV_set_integrable"\<close>
  have "(\<integral>\<^sup>+t\<in>{f..}. \<bar>$v.^t * $p_{t&x}\<bar> \<partial>lborel) \<le> (\<integral>\<^sup>+t\<in>{f..}. $v.^t \<partial>lborel)"
    by (rule nn_set_integral_mono; simp add: assms mult_left_le)
  also have "\<dots> < \<infinity>" using assms v_pos v_lt_1_iff_i_pos by (rewrite nn_integral_powr_Ici; simp)
  finally have "(\<integral>\<^sup>+t\<in>{f..}. \<bar>$v.^t * $p_{t&x}\<bar> \<partial>lborel) < \<infinity>" .
  moreover have "set_borel_measurable lborel {f..} (\<lambda>t::real. $v .^ t * $p_{t&x})"
    unfolding set_borel_measurable_def using assms by simp
  ultimately show  APV_set_integrable: "set_integrable lborel {f..} (\<lambda>t. $v.^t * $p_{t&x})"
    by (rewrite set_integrable_iff_bounded; simp)

  text \<open>Proof of "APV_calc"\<close>
  have "ennAPV x = (\<integral>\<^sup>+t\<in>{f..}. $v.^(tpl t) * $p_{t&x} \<partial>(IM abl))"
    by (rule ennAPV_nn_integral_interval_measure_abl, simp add: assms)
  also have "\<dots> = (\<integral>\<^sup>+t\<in>{f..}. $v.^t * $p_{t&x} \<partial>lborel)"
    unfolding tpl_def by (rule set_nn_integral_interval_measure_abl; simp add: assms)
  also have "\<dots> = (LBINT t:{f..}. $v.^t * $p_{t&x})"
    by (rewrite set_nn_integral_eq_set_integral; simp add: APV_set_integrable assms)
  finally have enn: "ennAPV x = (LBINT t:{f..}. $v.^t * $p_{t&x})" .
  hence "ennAPV x < \<infinity>" by simp
  moreover have "\<And>\<theta>. \<theta> > 0 \<Longrightarrow> (\<integral>\<^sup>+t. $v.^(tp \<theta> t) \<partial>(IM (ab \<theta>))) < \<infinity>"
  proof -
    fix \<theta>::real assume "\<theta> > 0" 
    have "(\<integral>\<^sup>+t. $v.^(tp \<theta> t) \<partial>(IM (ab \<theta>))) = (\<integral>\<^sup>+t\<in>{f..<\<theta>}. $v.^t \<partial>(IM abl))"
      by (rewrite PV_abl_tpl; simp add: tpl_def)
    also have "\<dots> = (\<integral>\<^sup>+t\<in>{f..<\<theta>}. $v.^t \<partial>lborel)"
      by (rule set_nn_integral_interval_measure_abl) auto
    also have "\<dots> \<le> (\<integral>\<^sup>+t\<in>{f..\<theta>}. $v.^t \<partial>lborel)"
      by (rule nn_set_integral_set_mono, simp add: atLeastLessThan_subseteq_atLeastAtMost_iff)
    also have "\<dots> < \<infinity>"
      using v_lt_1_iff_i_pos v_pos assms by (rewrite nn_integral_powr_Icc_gen; simp)
    finally show "(\<integral>\<^sup>+t. $v.^(tp \<theta> t) \<partial>(IM (ab \<theta>))) < \<infinity>" .
  qed
  ultimately have "APV x = ennAPV x" using ennAPV_APV by simp
  with enn show "APV x = (LBINT t:{f..}. $v.^t * $p_{t&x})"
    using ennreal_inj assms APV_nonneg by simp
qed

end

subsection \<open>Deferred Continuous Term Life Annuity\<close>

locale val_defer_cont_term_life_ann = actuarial_model +
  fixes f n :: real
  assumes f_nonneg[simp]: "f \<ge> 0" and
    n_nonneg[simp]: "n \<ge> 0"
begin

definition abl :: "real \<Rightarrow> real" where "abl t \<equiv> max (min t (f + n) - f) 0"

definition tpl :: "real \<Rightarrow> real" where "tpl t = t"

lemma abl_f_0[simp]:
  fixes t::real
  assumes "t < f"
  shows "abl t = 0"
  unfolding abl_def using assms by simp

lemma abl_f_fn:
  fixes t::real
  assumes "f \<le> t" "t < f + n"
  shows "abl t = t - f"
  unfolding abl_def using assms by simp

lemma abl_fn:
  fixes t::real
  assumes "f + n \<le> t"
  shows "abl t = n"
  unfolding abl_def using assms by simp

lemma abl_continuous[simp]:
  fixes t::real
  shows "isCont abl t"
  unfolding abl_def by (simp add: continuous_max continuous_min)

corollary
  fixes t::real
  shows abl_right_continuous[simp]: "continuous (at_right t) abl" and
    abl_left_continuous[simp]: "continuous (at_left t) abl"
  by (simp add: continuous_at_imp_continuous_within)+

lemma abl_mono[simp]: "mono abl"
  unfolding abl_def by (simp add: monoI)

lemma tpl_measurable[measurable]: "tpl \<in> borel_measurable borel"
  unfolding tpl_def by simp

end

sublocale val_defer_cont_term_life_ann \<subseteq> val_living i l f abl tpl
  by (standard; simp)

context val_defer_cont_term_life_ann
begin

lemma abl_eq_fn:
  fixes t::real
  assumes "t \<ge> f + n"
  shows "abl t = abl (f + n)"
  unfolding abl_def using assms by simp

end

sublocale val_defer_cont_term_life_ann \<subseteq> val_term_life_living i l f abl tpl n
  apply (standard, simp)
  by (rule abl_eq_fn) simp

context val_defer_cont_term_life_ann
begin

lemma DERIV_abl:
  fixes t::real
  assumes "f < t" "t < f + n"
  shows "DERIV abl t :> 1"
proof -
  have "DERIV (\<lambda>s. s - f) t :> 1 - 0" by (intro derivative_intros)
  thus "DERIV abl t :> 1"
    apply (rewrite DERIV_cong_ev; simp)
    apply (rewrite eventually_nhds_metric)
    by (rule exI[of _ "min (t-f) (f+n-t)"], auto simp add: assms abl_def dist_real_def)
qed

corollary abl_differentiable_on_f_fn : "abl differentiable_on {f <..< f+n}"
  by (meson DERIV_abl differentiable_at_withinI differentiable_on_def
      greaterThanLessThan_iff real_differentiable_def)

corollary deriv_abl:
  fixes t::real
  assumes "f < t" "t < f + n"
  shows "deriv abl t = 1"
  using assms DERIV_abl DERIV_imp_deriv by blast

lemma set_nn_integral_interval_measure_abl:
  fixes g :: "real \<Rightarrow> real" and A :: "real set"
  assumes "g \<in> borel_measurable borel" and
    A_borel: "A \<in> sets borel" "A \<subseteq> {f..f+n}"
  shows "(\<integral>\<^sup>+t\<in>A. g t \<partial>(IM abl)) = (\<integral>\<^sup>+t\<in>A. g t \<partial>lborel)"
proof -

  wlog A_f_fn: "A \<subseteq> {f<..<f+n}" generalizing A keeping A_borel
  proof -
    have "(\<integral>\<^sup>+t\<in>A. g t \<partial>(IM abl)) = (\<integral>\<^sup>+t\<in>A-{f}. g t \<partial>(IM abl))"
      using assms interval_measure_singleton_continuous
      by (rewrite nn_integral_minus_null; simp add: null_sets_def)
    also have "\<dots> = (\<integral>\<^sup>+t\<in>A-{f}-{f+n}. g t \<partial>(IM abl))"
      using assms interval_measure_singleton_continuous
      by (rewrite nn_integral_minus_null; simp add: null_sets_def)
    also have "\<dots> = (\<integral>\<^sup>+t\<in>A-{f}-{f+n}. g t \<partial>lborel)"
      using hypothesis[of "A-{f}-{f+n}"] assms by force
    also have "\<dots> = (\<integral>\<^sup>+t\<in>A-{f}. g t \<partial>lborel)"
      using assms by (rewrite nn_integral_minus_null[THEN sym]; force)
    also have "\<dots> = (\<integral>\<^sup>+t\<in>A. g t \<partial>lborel)"
      using assms by (rewrite nn_integral_minus_null[THEN sym]; force)
    finally show ?thesis .
  qed

  thus ?thesis
  proof -
    have "(\<integral>\<^sup>+t\<in>A. g t \<partial>(IM abl)) = (\<integral>\<^sup>+t\<in>A. ennreal (g t) * ennreal (deriv abl t) \<partial>lborel)"
      using assms A_borel A_f_fn abl_differentiable_on_f_fn deriv_abl
      by (rewrite set_nn_integral_interval_measure_deriv[of abl f "f+n"]; simp)
    also have "\<dots> = (\<integral>\<^sup>+t\<in>A. g t \<partial>lborel)"
      apply (intro set_nn_integral_cong)
      using deriv_abl A_f_fn by force+
    finally show ?thesis .
  qed
qed

lemma
  fixes x::real
  assumes "x < $\<psi>"
  shows APV_set_integrable: "set_integrable lborel {f..f+n} (\<lambda>t. $v.^t * $p_{t&x})" and
    APV_calc: "APV x = (LBINT t:{f..f+n}. $v.^t * $p_{t&x})"
proof -

  text \<open>Proof of "APV_set_integrable"\<close>
  have "set_integrable lborel {f..f+n} (\<lambda>t. $v.^t)"
    using v_pos by (rule set_integrable_powr_Icc)
  moreover have " set_borel_measurable lborel {f..f+n} (\<lambda>t. $v.^t * $p_{t&x})"
    unfolding set_borel_measurable_def using assms by simp
  moreover have "AE t\<in>{f..f+n} in lborel. norm ($v.^t * $p_{t&x}) \<le> norm ($v.^t)"
    using v_pos p_le_1 assms by simp
  ultimately show APV_set_integrable: "set_integrable lborel {f..f+n} (\<lambda>t. $v.^t * $p_{t&x})"
    by (rule set_integrable_bound)

  text \<open>Proof of "APV_calc"\<close>
  have "ennAPV x = (\<integral>\<^sup>+t\<in>{f..f+n}. $v.^(tpl t) * $p_{t&x} \<partial>(IM abl))"
    by (rule ennAPV_term_nn_integral_interval_measure_abl, simp add: assms)
  also have "\<dots> = (\<integral>\<^sup>+t\<in>{f..f+n}. $v.^t * $p_{t&x} \<partial>lborel)"
    unfolding tpl_def by (rule set_nn_integral_interval_measure_abl; simp add: assms)
  also have "\<dots> = (LBINT t:{f..f+n}. $v.^t * $p_{t&x})"
    using APV_set_integrable assms v_pos by (rewrite set_nn_integral_eq_set_integral; simp)
  finally have enn: "ennAPV x = (LBINT t:{f..f+n}. $v.^t * $p_{t&x})" .
  hence "ennAPV x < \<infinity>" by simp
  moreover have "\<And>\<theta>. \<theta> > 0 \<Longrightarrow> (\<integral>\<^sup>+t. $v.^(tp \<theta> t) \<partial>(IM (ab \<theta>))) < \<infinity>"
  proof -
    fix \<theta>::real assume "\<theta> > 0"
    have "(\<integral>\<^sup>+t. $v.^(tp \<theta> t) \<partial>(IM (ab \<theta>))) = (\<integral>\<^sup>+t\<in>{f..<\<theta>}. $v.^t \<partial>(IM abl))"
      by (rewrite PV_abl_tpl; simp add: tpl_def)
    also have "\<dots> = (\<integral>\<^sup>+t\<in>{f..< min (f+n) \<theta>}. $v.^t \<partial>(IM abl))"
    proof -
      have "(\<integral>\<^sup>+t\<in>{f..<\<theta>}. $v.^t \<partial>(IM abl)) =
        (\<integral>\<^sup>+t\<in>{f..< min (f+n) \<theta>} \<union> {min (f+n) \<theta> ..<\<theta>}. $v.^t \<partial>(IM abl))"
        apply (rule set_nn_integral_cong, simp)
        using less_eq_real_def n_nonneg by force+
      also have "\<dots> = (\<integral>\<^sup>+t\<in>{f..< min (f+n) \<theta>}. $v.^t \<partial>(IM abl)) +
        (\<integral>\<^sup>+t\<in>{min (f+n) \<theta> ..<\<theta>}. $v.^t \<partial>(IM abl))"
        by (rewrite nn_integral_disjoint_pair; simp)
      also have "(\<integral>\<^sup>+t\<in>{min (f+n) \<theta> ..<\<theta>}. $v.^t \<partial>(IM abl)) = 0"
      proof -
        have "abl - (\<lambda>_. n) constant_on {min (f + n) \<theta> <..<\<theta>}"
          unfolding fun_diff_def constant_on_def
          by (rule exI[of _ 0], safe, rewrite abl_fn; force)
        thus ?thesis
          using interval_measure_const_null
          by (rewrite Ico_Cont_nn_integral_interval_measure_cong[of abl "\<lambda>_. n"]; simp)
        qed
      finally show ?thesis by simp
    qed
    also have "\<dots> = (\<integral>\<^sup>+t\<in>{f..< min (f+n) \<theta>}. $v.^t \<partial>lborel)"
      by (rule set_nn_integral_interval_measure_abl) auto
    also have "\<dots> \<le> (\<integral>\<^sup>+t\<in>{f.. min (f+n) \<theta>}. $v.^t \<partial>lborel)"
      by (rule nn_set_integral_set_mono, simp add: atLeastLessThan_subseteq_atLeastAtMost_iff)
    also have "\<dots> < \<infinity>" using nn_integral_powr_Icc_finite v_pos by simp
    finally show "(\<integral>\<^sup>+t. $v.^(tp \<theta> t) \<partial>(IM (ab \<theta>))) < \<infinity>" .
  qed
  ultimately have "APV x = ennAPV x" using ennAPV_APV by simp
  with enn show "APV x = (LBINT t:{f..f+n}. $v.^t * $p_{t&x})"
    using ennreal_inj assms APV_nonneg by simp

qed

end

context actuarial_model
begin

definition APV_defer_cont_whole_life_ann :: "real \<Rightarrow> real \<Rightarrow> real" (\<open>$a'''_{_\<bar>_}\<close> [0,0] 200)
  where "$a'_{f\<bar>x} \<equiv> val.APV i l
    (val_living.ab (val_defer_cont_whole_life_ann.abl f))
    (val_living.tp val_defer_cont_whole_life_ann.tpl) x"

abbreviation APV_cont_whole_life_ann :: "real \<Rightarrow> real" (\<open>$a'''_{_}\<close> [0] 200)
  where "$a'_{x} \<equiv> $a'_{0\<bar>x}"

proposition
  a'_defer_whole_life_set_integrable: "set_integrable lborel {f..} (\<lambda>t. $v.^t * $p_{t&x})" and
  a'_defer_whole_life_calc: "$a'_{f\<bar>x} = (LBINT t:{f..}. $v.^t * $p_{t&x})"
  if "f \<ge> 0" "i > 0" "x < $\<psi>" for f x :: real
proof -
  have [simp]: "val_defer_cont_whole_life_ann i l f"
    apply (intro val_defer_cont_whole_life_ann.intro, simp add: actuarial_model_axioms)
    using that by (intro val_defer_cont_whole_life_ann_axioms.intro) simp
  show "set_integrable lborel {f..} (\<lambda>t. $v.^t * $p_{t&x})"
    by (rule val_defer_cont_whole_life_ann.APV_set_integrable; simp add: that)
  show "$a'_{f\<bar>x} = (LBINT t:{f..}. $v.^t * $p_{t&x})"
    unfolding APV_defer_cont_whole_life_ann_def using that
    by (rewrite val_defer_cont_whole_life_ann.APV_calc; simp)
qed

proposition a'_whole_life_calc: "$a'_{x} = (LBINT t:{0..}. $v.^t * $p_{t&x})"
  if "i > 0" "x < $\<psi>" for x::real
  using that a'_defer_whole_life_calc by simp

definition
  APV_defer_cont_term_life_ann :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" (\<open>$a'''_{_\<bar>_;_\<rceil>}\<close> [0,0,0] 200)
  where "$a'_{f\<bar>x;n\<rceil>} \<equiv> val.APV i l
    (val_living.ab (val_defer_cont_term_life_ann.abl f n))
    (val_living.tp val_defer_cont_term_life_ann.tpl) x"

abbreviation APV_cont_term_life_ann :: "real \<Rightarrow> real \<Rightarrow> real" (\<open>$a'''_{_;_\<rceil>}\<close> [0,0] 200)
  where "$a'_{x;n\<rceil>} \<equiv> $a'_{0\<bar>x;n\<rceil>}"

proposition 
  a'_defer_term_life_set_integrable: "set_integrable lborel {f..f+n} (\<lambda>t. $v.^t * $p_{t&x})" and
  a'_defer_term_life_calc: "$a'_{f\<bar>x;n\<rceil>} = (LBINT t:{f..f+n}. $v.^t * $p_{t&x})"
  if "f \<ge> 0" "n \<ge> 0" "x < $\<psi>" for f n x :: real
proof -
  have [simp]: "val_defer_cont_term_life_ann i l f n"
    apply (intro val_defer_cont_term_life_ann.intro, simp add: actuarial_model_axioms)
    using that by (intro val_defer_cont_term_life_ann_axioms.intro) simp
  show "set_integrable lborel {f..f+n} (\<lambda>t. $v.^t * $p_{t&x})"
    by (rule val_defer_cont_term_life_ann.APV_set_integrable; simp add: that)
  show "$a'_{f\<bar>x;n\<rceil>} = (LBINT t:{f..f+n}. $v.^t * $p_{t&x})"
    unfolding APV_defer_cont_term_life_ann_def using that
    by (rewrite val_defer_cont_term_life_ann.APV_calc; simp)
qed

proposition a'_term_life_calc: "$a'_{x;n\<rceil>} = (LBINT t:{0..n}. $v.^t * $p_{t&x})"
  if "n \<ge> 0" "x < $\<psi>" for n x :: real
  using that a'_defer_term_life_calc by simp

lemma a'_defer_whole_term_life_beyond: "$a'_{f\<bar>x} = $a'_{f\<bar>x;n\<rceil>}"
  if "x+f+n \<ge> $\<psi>" "f \<ge> 0" "n \<ge> 0" "i > 0" "x < $\<psi>" for f n x :: real
proof -
  interpret limited_life_table
    apply standard
    using that l_0_equiv[of "x+f+n"] by blast
  have "$a'_{f\<bar>x} = (LBINT t:{f..}. $v.^t * $p_{t&x})"
    using that by (rewrite a'_defer_whole_life_calc; simp)
  also have "\<dots> = (LBINT t:{f..f+n}. $v.^t * $p_{t&x}) + (LBINT t:{f+n<..}. $v.^t * $p_{t&x})"
  proof -
    have [simp]: "{f+n<..} \<subseteq> {f..}" using that by auto
    have [simp]: "{f..f+n} \<inter> {f+n<..} = {}" using that by auto
    have [simp]: "{f..f+n} \<union> {f+n<..} = {f..}" using that by auto
    have "set_integrable lborel {f+n<..} (\<lambda>t. $v.^t * $p_{t&x})"
      by (rule set_integrable_subset[OF a'_defer_whole_life_set_integrable, of f])
        (auto simp add: that)
    thus ?thesis
      using a'_defer_term_life_set_integrable that by (rewrite set_integral_Un[THEN sym]; simp)
  qed
  also have "(LBINT t:{f+n<..}. $v.^t * $p_{t&x}) = 0"
  proof -
    { fix t assume "t \<in> {f+n<..}"
      hence "f + n < t" by simp
      hence "$\<psi> \<le> x + t" using that le_ereal_le by auto
      hence "$v.^t * $p_{t&x} = 0" using p_0_equiv that by simp }
    thus ?thesis by (rewrite set_lebesgue_integral_cong[where g="\<lambda>_. 0"]; simp)
  qed
  finally show ?thesis using a'_defer_term_life_calc that by simp
qed

lemma a'_whole_term_life_beyond: "$a'_{x} = $a'_{x;n\<rceil>}"
  if "x+n \<ge> $\<psi>" "n \<ge> 0" "i > 0" "x < $\<psi>" for f n x :: real
  using a'_defer_whole_term_life_beyond that by simp

end

(* locale limited_actuarial_model = interest + limited_life_table

sublocale limited_actuarial_model \<subseteq> actuarial_model
  by standard

context limited_actuarial_model
begin

 lemma a'_defer_whole_term_life_beyond_nat: "$a'_{f\<bar>x} = $a'_{f\<bar>x;n}"
  if "x+f+n \<ge> $\<omega>" "i > 0" "x < $\<omega>" for f n x :: nat
  using psi_le_iff_omega_le x_lt_psi a'_defer_whole_term_life_beyond that
  by (metis (no_types, lifting) of_nat_0_le_iff of_nat_add)

lemma a'_whole_term_life_beyond_nat: "$a'_{x} = $a'_{x;n}"
  if "x+n \<ge> $\<omega>" "i > 0" "x < $\<omega>" for f n x :: nat
  using psi_le_iff_omega_le x_lt_psi a'_whole_term_life_beyond that
  by (metis of_nat_0_le_iff of_nat_add)

end
 *)

end

