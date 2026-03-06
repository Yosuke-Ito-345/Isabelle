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

(* delete if this is used only for proving lemma ennAPV_vp_abg *)
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

subsection \<open>Actuarial Present Value\<close>

subsubsection \<open>Framework\<close>

text \<open>
  In this theory, I describe various kinds of life insurance benefits and annuities in a uniform way.
  This allows us to generally define the actuarial present values of life contingencies.
\<close>

locale actuarial_model = interest + life_table

text \<open>
  In the following locale "val", I adopt some abbreviations for actuarial terms.
      (i) "ab" stands for "accumulated benefit".
     (ii) "tp" stands for "time of payment".
    (iii) "PVs" stands for "present value".
          I add the suffix "s", representing "sample path",
          to distinguish the present value in "Annuity.thy".
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
    ennPVs_measurable[measurable]: "(\<lambda>\<theta>. \<integral>\<^sup>+t. $v.^(tp \<theta> t) \<partial>(IM (ab \<theta>))) \<in> borel_measurable borel"
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

lemma PVs_measurable[measurable]: "(\<lambda>\<theta>. \<integral>t. $v.^(tp \<theta> t) \<partial>(IM (ab \<theta>))) \<in> borel_measurable borel"
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
  thus ?thesis using borel_measurable_enn2real ennPVs_measurable by simp
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
  have "\<And>\<xi>. \<xi> \<in> space (\<MM> \<downharpoonright> alive x) \<Longrightarrow> integrable (IM (ab (T x \<xi>))) (\<lambda>t. $v.^(tp (T x \<xi>) t))"
    using assms by (intro integrableI_bounded; simp)
  hence "ennAPV x = \<integral>\<^sup>+\<xi>. ennreal (\<integral>t. $v.^(tp (T x \<xi>) t) \<partial>(IM (ab (T x \<xi>)))) \<partial>(\<MM> \<downharpoonright> alive x)"
    unfolding ennAPV_def apply (intro nn_integral_cong)
    by (rewrite nn_integral_eq_integral; simp)
  also have "\<dots> = ennreal (APV x)"
  proof -
    have " integrable (\<MM> \<downharpoonright> alive x) (\<lambda>\<xi>. LINT t | IM (ab (T x \<xi>)). $v.^(tp (T x \<xi>) t))"
      using calculation assms by (intro integrableI_bounded; simp)
    thus ?thesis
      unfolding APV_def by (rewrite nn_integral_eq_integral; simp)
  qed
  finally show ?thesis .
qed

end

subsubsection \<open>Term Life\<close>

locale val_term_life = val +
  fixes n::real
  assumes n_nonneg[simp]: "n \<ge> 0" and
    ab_eq_fn: "\<And>\<theta> t. t \<ge> f + n \<Longrightarrow> ab \<theta> t = ab \<theta> (f + n)"
begin

lemma ab_constant_on_fn:
  fixes \<theta>::real
  shows "(ab \<theta>) constant_on {f+n..}"
  using ab_eq_fn by (meson atLeast_iff constant_on_def)

end

subsubsection \<open>Life Annuity\<close>

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
proof -
  have "\<And>s t. s \<le> t \<Longrightarrow> abg s \<le> abg t"
    using abg_mono monoD by blast
  moreover have "\<And>t. t < \<theta> \<Longrightarrow> abg t \<le> abg \<theta>"
    using abg_mono monoD order_less_imp_le by blast
  ultimately show ?thesis
    using Lim_left_bound[of UNIV \<theta> abg "abg \<theta>"] by simp
qed

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

lemma ennPVs_abg:
  fixes \<theta>::real
  shows "(\<integral>\<^sup>+t. $v.^(tp \<theta> t) \<partial>(IM (ab \<theta>))) = (\<integral>\<^sup>+t\<in>{f..<\<theta>}. $v.^t \<partial>(IM abg))"
proof -
  have "ab \<theta> constant_on {\<theta><..}"
    using ab_constant_on_th by (meson Ioi_le_Ico constant_on_subset)
  hence "(\<integral>\<^sup>+t. $v.^(tp \<theta> t) \<partial>(IM (ab \<theta>))) = (\<integral>\<^sup>+t\<in>{f..<\<theta>}. $v.^t \<partial>(IM (ab \<theta>)))"
    unfolding tp_def using isCont_ab_th ab_constant_on_f
    by (rewrite nn_integral_interval_measure_Ico; simp)
  also have "\<dots> = (\<integral>\<^sup>+t\<in>{f..<\<theta>}. $v.^t \<partial>(IM abg))"
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

lemma ennPVs_abg_fin:
  fixes \<theta>::real
  shows "(\<integral>\<^sup>+t\<in>{f..<\<theta>}. $v.^t \<partial>(IM abg)) < \<infinity>"
proof -
  have "\<And>t. f \<le> t \<and> t < \<theta> \<Longrightarrow> ennreal ($v.^t) \<le> ennreal (max ($v.^f) ($v.^\<theta>))"
    using ennreal_leI by (smt (verit) f_nonneg powr_less_mono powr_mono_both' v_pos)
  thus "(\<integral>\<^sup>+t\<in>{f..<\<theta>}. $v.^t \<partial>(IM abg)) < \<infinity>"
    by (intro set_nn_integral_interval_measure_bounded_finite[where M="max ($v.^f) ($v.^\<theta>)"]; simp)
qed

lemma PVs_abg_set_integrable:
  fixes \<theta>::real
  shows "set_integrable (IM abg) {f..<\<theta>} (\<lambda>t. $v.^t)"
proof -
  have "set_borel_measurable (IM abg) {f..<\<theta>} (\<lambda>t. $v.^t)"
    unfolding set_borel_measurable_def by measurable
  then show ?thesis 
    using ennPVs_abg_fin by (rewrite set_integrable_iff_bounded) auto
qed

corollary ennPVs_abg_PVs:
  fixes \<theta>::real
  shows "(\<integral>\<^sup>+t\<in>{f..<\<theta>}. $v.^t \<partial>(IM abg)) = ennreal (\<integral>t\<in>{f..<\<theta>}. $v.^t \<partial>(IM abg))"
  using PVs_abg_set_integrable by (rewrite set_nn_integral_eq_set_integral; simp)

lemma ennPVs_abg_measurable[measurable]:
  "(\<lambda>\<theta>. (\<integral>\<^sup>+t\<in>{f..<\<theta>}. $v.^t \<partial>(IM abg))) \<in> borel_measurable borel"
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
  thus ?thesis by (simp add: nn_integral_set_ennreal)
qed

corollary ennPVs_fin:
  fixes \<theta>::real
  shows "(\<integral>\<^sup>+t. $v.^(tp \<theta> t) \<partial>(IM (ab \<theta>))) < \<infinity>"
  using ennPVs_abg_fin ennPVs_abg by simp

corollary PVs_integrable:
  fixes \<theta>::real
  shows "integrable (IM (ab \<theta>)) (\<lambda>t. $v.^(tp \<theta> t))"
  using ennPVs_fin by (rewrite integrable_iff_bounded; simp)

corollary ennPVs_PVs:
  fixes \<theta>::real
  shows "(\<integral>\<^sup>+t. $v.^(tp \<theta> t) \<partial>(IM (ab \<theta>))) = ennreal (\<integral>t. $v.^(tp \<theta> t) \<partial>(IM (ab \<theta>)))"
  using PVs_integrable by (rewrite nn_integral_eq_integral; simp)

corollary ennPVs_measurable[measurable]:
  "(\<lambda>\<theta>. \<integral>\<^sup>+t. $v.^(tp \<theta> t) \<partial>(IM (ab \<theta>))) \<in> borel_measurable borel"
  using ennPVs_abg ennPVs_abg_measurable by simp

end

sublocale val_life_ann \<subseteq> val i l f ab tp
  by (standard; simp)

context val_life_ann
begin

lemma ennAPV_ennPV_abg:
  assumes "x < $\<psi>"
  shows "ennAPV x = \<integral>\<^sup>+\<xi>. (\<integral>\<^sup>+t\<in>{f..< T x \<xi>}. $v.^t \<partial>(IM abg)) \<partial>(\<MM> \<downharpoonright> alive x)"
  unfolding ennAPV_def by (auto intro!: nn_integral_cong simp add: ennPVs_abg)

lemma APV_PV_abg:
  assumes "x < $\<psi>" "ennAPV x < \<infinity>"
  shows "APV x = \<integral>\<xi>. (\<integral>t\<in>{f..< T x \<xi>}. $v.^t \<partial>(IM abg)) \<partial>(\<MM> \<downharpoonright> alive x)"
proof -

  have "(\<lambda>\<theta>. (\<integral>t\<in>{f..<\<theta>}. $v.^t \<partial>(IM abg))) \<in> borel_measurable borel"
    using ennPVs_abg_PVs ennPVs_abg_measurable by simp
  hence [measurable]: "(\<lambda>\<xi>. set_lebesgue_integral (IM abg) {f..<T x \<xi>} ((.^) ($v)))
    \<in> borel_measurable (\<MM> \<downharpoonright> alive x)"
    using PVs_measurable by simp

  have "ennreal (APV x) = ennAPV x"
    using ennPVs_fin assms by (rewrite ennAPV_APV; simp)
  also have ennAPV': "\<dots> = (\<integral>\<^sup>+\<xi>. ennreal (\<integral>t\<in>{f..< T x \<xi>}. $v.^t \<partial>(IM abg)) \<partial>(\<MM> \<downharpoonright> alive x))"
    apply (rewrite ennAPV_ennPV_abg, simp add: assms)
    apply (rule nn_integral_cong)
    by (rule set_nn_integral_eq_set_integral; simp add: PVs_abg_set_integrable)
  also have "\<dots> = ennreal (\<integral>\<xi>. (\<integral>t\<in>{f..< T x \<xi>}. $v.^t \<partial>(IM abg)) \<partial>(\<MM> \<downharpoonright> alive x))"
    apply (rule nn_integral_eq_integral)
     apply (rule integrableI_nonneg)
    using ennAPV' assms by simp_all
  finally have "ennreal (APV x) = ennreal (\<integral>\<xi>. (\<integral>t\<in>{f..< T x \<xi>}. $v.^t \<partial>(IM abg)) \<partial>(\<MM> \<downharpoonright> alive x))" .
  then show ?thesis
    using APV_nonneg assms by (rewrite ennreal_inj[THEN sym]; simp)

qed

lemma ennAPV_vp_abg:
  assumes "x < $\<psi>"
  shows "ennAPV x = (\<integral>\<^sup>+t. $v.^t * $p_{t&x} \<partial>(IM abg))"
proof -
  { fix \<xi> assume "\<xi> \<in> space (\<MM> \<downharpoonright> alive x)"
    have "ab (T x \<xi>) constant_on {T x \<xi> <..}"
      using ab_constant_on_th by (meson Ioi_le_Ico constant_on_subset)
    hence "(\<integral>\<^sup>+t. ennreal ($v.^(tp (T x \<xi>) t)) \<partial>(IM (ab (T x \<xi>)))) = 
      (\<integral>\<^sup>+t\<in>{..< T x \<xi>}. ennreal ($v.^(tp (T x \<xi>) t)) \<partial>(IM (ab (T x \<xi>))))"
      by (rewrite nn_integral_interval_measure_Iio[where s="T x \<xi>"]; simp add: isCont_ab_th)
    also have "\<dots> = (\<integral>\<^sup>+t\<in>{..< T x \<xi>}. ennreal ($v.^(tp (T x \<xi>) t)) \<partial>(IM abg))"
      by (rule Iio_nn_integral_interval_measure_cong;
          simp add: fun_diff_def ab_eq_abg constant_on_def)
    also have "\<dots> = (\<integral>\<^sup>+t\<in>{..< T x \<xi>}. ennreal ($v.^t) \<partial>(IM abg))" unfolding tp_def by simp
    finally have
      "(\<integral>\<^sup>+t. ennreal ($v.^(tp (T x \<xi>) t)) \<partial>(IM (ab (T x \<xi>)))) =
        (\<integral>\<^sup>+t\<in>{..< T x \<xi>}. ennreal ($v.^t) \<partial>(IM abg))" . }
  hence "ennAPV x = \<integral>\<^sup>+\<xi>. (\<integral>\<^sup>+t\<in>{..< T x \<xi>}. ennreal ($v.^t) \<partial>(IM abg)) \<partial>(\<MM> \<downharpoonright> alive x)"
    unfolding ennAPV_def by (meson nn_integral_cong)
  also have "\<dots> = (\<integral>\<^sup>+t. $v.^t * $p_{t&x} \<partial>(IM abg))"
    using assms
    by (rewrite nn_integral_toTx_p; simp add: sigma_finite_interval_measure monoD ennreal_mult')
  finally show ?thesis .
qed

corollary ennAPV_vp_abg_f:
  assumes "x < $\<psi>"
  shows "ennAPV x = (\<integral>\<^sup>+t\<in>{f..}. $v.^t * $p_{t&x} \<partial>(IM abg))"
  apply (rewrite ennAPV_vp_abg, simp add: assms)
  by (rewrite nn_integral_interval_measure_Ici; simp add: fun_diff_def constant_on_def assms)

end

subsubsection \<open>Term Life Annuity\<close>

locale val_term_life_ann = val_life_ann + term_annuity
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
    hence "ab \<theta> t = abg t" using ab_eq_abg by simp
    also have "\<dots> = abg (f + n)" using abg_eq_fn assms by blast
    also have "\<dots> = ab \<theta> (f + n)" using fnth ab_eq_abg by simp
    finally show ?thesis .
  next
    case False
    hence "ab \<theta> t = Lim (at_left \<theta>) abg" using ab_eq_Lim_abg by simp
    also have "\<dots> = abg (f + n)"
    proof -
      have "\<And>s. s \<noteq> \<theta> \<Longrightarrow> s \<in> {f+n<..<\<theta>} \<Longrightarrow> abg s = abg (f + n)" by (rule abg_eq_fn) simp
      hence "(abg \<longlongrightarrow> abg (f + n)) (at_left \<theta>)"
        apply (rewrite at_within_Ioo_at_left[THEN sym, of "f+n"], simp add: fnth)
        by (rewrite Lim_cong_within[where g="\<lambda>_. abg (f+n)"]; simp) simp+
      thus ?thesis using tendsto_Lim by force
    qed
    also have "\<dots> = ab \<theta> (f + n)" using fnth ab_eq_abg by simp
    finally show ?thesis .
  qed
next
  case False
  thus ?thesis using ab_eq_Lim_abg assms by force
qed

end

sublocale val_term_life_ann \<subseteq> val_term_life i l f ab tp n
  apply (standard, simp)
  using ab_eq_fn by blast

context val_term_life_ann
begin

lemma ennAPV_vp_abg_fn:
  assumes "x < $\<psi>"
  shows "ennAPV x = (\<integral>\<^sup>+t\<in>{..f+n}. $v.^t * $p_{t&x} \<partial>(IM abg))"
proof -
  have "abg constant_on {f+n<..}"
    using abg_constant_on_fn by (meson Ioi_le_Ico constant_on_subset)
  thus "ennAPV x = (\<integral>\<^sup>+t\<in>{..f+n}. $v.^t * $p_{t&x} \<partial>(IM abg))"
    apply (rewrite ennAPV_vp_abg, simp add: assms)
    by (rewrite nn_integral_interval_measure_Iic; simp add: assms)
qed

lemma ennAPV_vp_abg_f_fn:
  assumes "x < $\<psi>"
  shows "ennAPV x = (\<integral>\<^sup>+t\<in>{f..f+n}. $v.^t * $p_{t&x} \<partial>(IM abg))"
proof -
  have [simp]: "abg constant_on {f+n<..}"
    using abg_constant_on_fn by (meson Ioi_le_Ico constant_on_subset)
  have "ennAPV x = (\<integral>\<^sup>+t. ennreal ($v.^t * $p_{t&x}) * indicator {f..} t \<partial>(IM abg))"
    using ennAPV_vp_abg_f assms by simp
  also have "\<dots> = (\<integral>\<^sup>+t\<in>{..f+n}. ennreal ($v.^t * $p_{t&x}) * indicator {f..} t \<partial>(IM abg))"
    using assms by (rewrite nn_integral_interval_measure_Iic; simp)
  also have "\<dots> = (\<integral>\<^sup>+t\<in>{f..f+n}. ennreal ($v.^t * $p_{t&x}) \<partial>(IM abg))"
    apply (rule nn_integral_cong)
    by (metis mult_1_right atLeastAtMost_iff atLeast_iff
        atMost_iff ennreal_mult_right_cong indicator_simps)
  finally show ?thesis .
qed

end

subsubsection \<open>Deferred Pure Endowment\<close>

locale val_defer_pure_endow = actuarial_model + unit_payment

sublocale val_defer_pure_endow \<subseteq> val_term_life_ann i l f abg
  by standard

context val_defer_pure_endow
begin

lemma ennAPV_calc: 
  fixes x::real
  assumes "x < $\<psi>"
  shows "ennAPV x = $v.^(f+n) * $p_{f+n&x}"
proof -
  have [simp]: "{..f+n} = {..<f+n} \<union> {f+n}"
    by force
  have [simp]: "(\<lambda>t. ennreal ($v.^t * $p_{t&x})) \<in> borel_measurable borel"
    using assms by measurable
  have "ennAPV x = (\<integral>\<^sup>+t\<in>{..f+n}. $v.^t * $p_{t&x} \<partial>(IM abg))"
    using ennAPV_vp_abg_fn assms by simp
  also have "\<dots> =
    (\<integral>\<^sup>+t\<in>{..<f+n}. $v.^t * $p_{t&x} \<partial>(IM abg)) + (\<integral>\<^sup>+t\<in>{f+n}. $v.^t * $p_{t&x} \<partial>(IM abg))"
    using assms by (rewrite nn_integral_disjoint_pair[THEN sym]; simp)
  moreover have "(\<integral>\<^sup>+t\<in>{..<f+n}. $v.^t * $p_{t&x} \<partial>(IM abg)) = 0"
    by (rewrite Iio_nn_integral_interval_measure_cong[where G="\<lambda>_. 0"];
        simp add: interval_measure_const_null constant_on_def)
  moreover have "(\<integral>\<^sup>+t\<in>{f+n}. $v.^t * $p_{t&x} \<partial>(IM abg)) = $v.^(f+n) * $p_{f+n&x}"
    using emeasure_fn_interval_measure_abg by simp
  ultimately show ?thesis
    by simp
qed

corollary ennAPV_fin:
  fixes x::real
  assumes "x < $\<psi>"
  shows "ennAPV x < \<infinity>"
  using ennAPV_calc assms by simp

corollary APV_calc:
  fixes x::real
  assumes "x < $\<psi>"
  shows "APV x = $v.^(f+n) * $p_{f+n&x}"
  using assms ennAPV_calc ennAPV_fin ennPVs_fin ennAPV_APV APV_nonneg
  by (metis enn2real_ennreal mult_nonneg_nonneg p_nonneg powr_ge_zero)

end

subsubsection \<open>Deferred Continuous Whole Life Annuity\<close>

locale val_defer_cont_whole_life_ann = actuarial_model + defer_cont_perp_ann

sublocale val_defer_cont_whole_life_ann \<subseteq> val_life_ann i l f abg
  by (standard; simp)

context val_defer_cont_whole_life_ann
begin

lemma ennAPV_calc: 
  fixes x::real
  assumes "x < $\<psi>"
  shows "ennAPV x = (\<integral>\<^sup>+t\<in>{f..}. $v.^t * $p_{t&x} \<partial>lborel)"
proof -
  have "ennAPV x = (\<integral>\<^sup>+t\<in>{f..}. $v.^t * $p_{t&x} \<partial>(IM abg))"
    by (rule ennAPV_vp_abg_f, simp add: assms)
  also have "\<dots> = (\<integral>\<^sup>+t\<in>{f..}. $v.^t * $p_{t&x} \<partial>lborel)"
    by (rule set_nn_integral_interval_measure_abg; simp add: assms)
  finally show ?thesis .
qed

lemma ennAPV_fin:
  fixes x::real
  assumes "i > 0" "x < $\<psi>"
  shows "ennAPV x < \<infinity>"
proof -
  have "ennAPV x \<le> (\<integral>\<^sup>+t\<in>{f..}. $v.^t \<partial>lborel)"
    apply (rewrite ennAPV_calc, simp add: assms)
    by (rule nn_set_integral_mono; simp add: assms mult_left_le)
  also have "\<dots> < \<infinity>" using assms v_pos v_lt_1_iff_i_pos by (rewrite nn_integral_powr_Ici; simp)
  finally show "ennAPV x < \<infinity>" .
qed

lemma
  fixes x::real
  assumes "i > 0" "x < $\<psi>"
  shows APV_set_integrable: "set_integrable lborel {f..} (\<lambda>t. $v.^t * $p_{t&x})" and
    APV_calc: "APV x = (LBINT t:{f..}. $v.^t * $p_{t&x})"
proof -

  text \<open>Proof of "APV_set_integrable"\<close>
  have "(\<integral>\<^sup>+t\<in>{f..}. \<bar>$v.^t * $p_{t&x}\<bar> \<partial>lborel) < \<infinity>"
    using ennAPV_calc ennAPV_fin assms by simp
  moreover have "set_borel_measurable lborel {f..} (\<lambda>t. $v.^t * $p_{t&x})"
    unfolding set_borel_measurable_def using assms by simp
  ultimately show APV_set_integrable: "set_integrable lborel {f..} (\<lambda>t. $v.^t * $p_{t&x})"
    by (rewrite set_integrable_iff_bounded; simp)

  text \<open>Proof of "APV_calc"\<close>
  have "ennreal (APV x) = ennAPV x"
    using ennAPV_fin ennPVs_fin ennAPV_APV assms by simp
  also have "\<dots> = ennreal (LBINT t:{f..}. $v.^t * $p_{t&x})"
    apply (rewrite ennAPV_calc, simp add: assms)
    using APV_set_integrable assms by (rewrite set_nn_integral_eq_set_integral; simp)
  finally show "APV x = (LBINT t:{f..}. $v.^t * $p_{t&x})"
    using ennreal_inj assms APV_nonneg by simp

qed

end

subsubsection \<open>Deferred Continuous Term Life Annuity\<close>

locale val_defer_cont_term_life_ann = actuarial_model + defer_cont_term_ann

sublocale val_defer_cont_term_life_ann \<subseteq> val_term_life_ann i l f abg n
  by (standard; simp)

context val_defer_cont_term_life_ann
begin

lemma ennAPV_calc: 
  fixes x::real
  assumes "x < $\<psi>"
  shows "ennAPV x = (\<integral>\<^sup>+t\<in>{f..f+n}. $v.^t * $p_{t&x} \<partial>lborel)"
proof -
  have "ennAPV x = (\<integral>\<^sup>+t\<in>{f..f+n}. $v.^t * $p_{t&x} \<partial>(IM abg))"
    by (rule ennAPV_vp_abg_f_fn, simp add: assms)
  also have "\<dots> = (\<integral>\<^sup>+t\<in>{f..f+n}. $v.^t * $p_{t&x} \<partial>lborel)"
    by (rule set_nn_integral_interval_measure_abg; simp add: assms)
  finally show ?thesis .
qed

lemma ennAPV_fin:
  fixes x::real
  assumes "x < $\<psi>"
  shows "ennAPV x < \<infinity>"
proof -
  have "ennAPV x \<le> (\<integral>\<^sup>+t\<in>{f..f+n}. $v.^t \<partial>lborel)"
    apply (rewrite ennAPV_calc, simp add: assms)
    by (rule nn_set_integral_mono; simp add: assms mult_left_le)
  also have "\<dots> < \<infinity>"
    using nn_integral_powr_Icc_finite v_pos by simp
  finally show "ennAPV x < \<infinity>" .
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
  have "ennreal (APV x) = ennAPV x"
    using ennPVs_fin ennAPV_APV ennAPV_fin assms by (rewrite ennAPV_APV; simp)
  also have "\<dots> = ennreal (LBINT t:{f..f+n}. $v.^t * $p_{t&x})"
    apply (rewrite ennAPV_calc, simp add: assms)
    using APV_set_integrable assms v_pos by (rewrite set_nn_integral_eq_set_integral; simp)
  finally show "APV x = (LBINT t:{f..f+n}. $v.^t * $p_{t&x})"
    using ennreal_inj assms APV_nonneg by simp

qed

end

subsection \<open>Actuarial Notation\<close>

context actuarial_model
begin

definition APV_defer_cont_whole_life_ann :: "real \<Rightarrow> real \<Rightarrow> real" (\<open>$a'''_{_\<bar>_}\<close> [0,0] 200)
  where "$a'_{f\<bar>x} \<equiv> val.APV i l
    (val_life_ann.ab (defer_cont_perp_ann.abg f)) val_life_ann.tp x"

abbreviation APV_cont_whole_life_ann :: "real \<Rightarrow> real" (\<open>$a'''_{_}\<close> [0] 200)
  where "$a'_{x} \<equiv> $a'_{0\<bar>x}"

proposition
  a'_defer_whole_life_set_integrable: "set_integrable lborel {f..} (\<lambda>t. $v.^t * $p_{t&x})" and
  a'_defer_whole_life_calc: "$a'_{f\<bar>x} = (LBINT t:{f..}. $v.^t * $p_{t&x})"
  if "f \<ge> 0" "i > 0" "x < $\<psi>" for f x :: real
proof -
  have [simp]: "val_defer_cont_whole_life_ann i l f"
    by standard (rule that)
  show "set_integrable lborel {f..} (\<lambda>t. $v.^t * $p_{t&x})"
    by (rule val_defer_cont_whole_life_ann.APV_set_integrable; simp add: that)
  show "$a'_{f\<bar>x} = (LBINT t:{f..}. $v.^t * $p_{t&x})"
    unfolding APV_defer_cont_whole_life_ann_def using that
    by (rewrite val_defer_cont_whole_life_ann.APV_calc; simp)
qed

proposition
  a'_whole_life_set_integrable: "set_integrable lborel {0..} (\<lambda>t. $v.^t * $p_{t&x})" and
  a'_whole_life_calc: "$a'_{x} = (LBINT t:{0..}. $v.^t * $p_{t&x})"
  if "i > 0" "x < $\<psi>" for x::real
  using that a'_defer_whole_life_set_integrable a'_defer_whole_life_calc by simp+

definition
  APV_defer_cont_term_life_ann :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" (\<open>$a'''_{_\<bar>_;_\<rceil>}\<close> [0,0,0] 200)
  where "$a'_{f\<bar>x;n\<rceil>} \<equiv> val.APV i l
    (val_life_ann.ab (defer_cont_term_ann.abg f n)) val_life_ann.tp x"

abbreviation APV_cont_term_life_ann :: "real \<Rightarrow> real \<Rightarrow> real" (\<open>$a'''_{_;_\<rceil>}\<close> [0,0] 200)
  where "$a'_{x;n\<rceil>} \<equiv> $a'_{0\<bar>x;n\<rceil>}"

proposition 
  a'_defer_term_life_set_integrable: "set_integrable lborel {f..f+n} (\<lambda>t. $v.^t * $p_{t&x})" and
  a'_defer_term_life_calc: "$a'_{f\<bar>x;n\<rceil>} = (LBINT t:{f..f+n}. $v.^t * $p_{t&x})"
  if "f \<ge> 0" "n \<ge> 0" "x < $\<psi>" for f n x :: real
proof -
  have [simp]: "val_defer_cont_term_life_ann i l f n"
    by (standard; simp add: that)
  show "set_integrable lborel {f..f+n} (\<lambda>t. $v.^t * $p_{t&x})"
    by (rule val_defer_cont_term_life_ann.APV_set_integrable; simp add: that)
  show "$a'_{f\<bar>x;n\<rceil>} = (LBINT t:{f..f+n}. $v.^t * $p_{t&x})"
    unfolding APV_defer_cont_term_life_ann_def using that
    by (rewrite val_defer_cont_term_life_ann.APV_calc; simp)
qed

proposition
  a'_term_life_set_integrable: "set_integrable lborel {0..n} (\<lambda>t. $v.^t * $p_{t&x})" and
  a'_term_life_calc: "$a'_{x;n\<rceil>} = (LBINT t:{0..n}. $v.^t * $p_{t&x})"
  if "n \<ge> 0" "x < $\<psi>" for n x :: real
  using that a'_defer_term_life_set_integrable[of 0] a'_defer_term_life_calc by simp+

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
      by (rule set_integrable_subset[OF a'_defer_whole_life_set_integrable, of f], auto intro: that)
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

lemma a'_whole_life_term_Tx: "$a'_{x} = \<integral>\<xi>. $a'_(T x \<xi>)\<rceil> \<partial>(\<MM> \<downharpoonright> alive x)"
  if "i > 0" "x < $\<psi>" for x::real
proof -

  interpret cpa: defer_cont_perp_ann i 0
    apply (intro defer_cont_perp_ann.intro)
    apply (rule interest_axioms)
    by (simp add: defer_cont_perp_ann_axioms.intro)
  interpret vcwla: val_defer_cont_whole_life_ann i l 0
    apply (rule val_defer_cont_whole_life_ann.intro)
     apply (rule actuarial_model_axioms)
    by (metis cpa.defer_cont_perp_ann_axioms)

  { fix \<xi> assume xi_in: "\<xi> \<in> space (\<MM> \<downharpoonright> alive x)"

    have "sym_diff {0..< T x \<xi>} {0.. T x \<xi>} = {T x \<xi>}"
      using less_eq_real_def xi_in by force
    hence sdTx: "sym_diff {0..< T x \<xi>} {0.. T x \<xi>} \<in> null_sets (IM cpa.abg)"
      by (simp add: interval_measure_singleton_continuous null_setsI)

    interpret dcta: defer_cont_term_ann i 0 "T x \<xi>"
      apply (intro defer_cont_term_ann.intro)
       apply (rule interest_axioms)
      apply (intro defer_cont_term_ann_axioms.intro, simp)
      using xi_in that alivex_Tx_pos less_eq_real_def by force

    have [simp]: "cpa.abg - dcta.abg constant_on {0<.. T x \<xi>}"
      unfolding cpa.abg_def dcta.abg_def constant_on_def
      by (rule exI[of _ 0]) simp

    have "ennreal (\<integral>t\<in>{0..< T x \<xi>}. $v.^t \<partial>(IM cpa.abg)) = (\<integral>\<^sup>+t\<in>{0..< T x \<xi>}. $v.^t \<partial>(IM cpa.abg))"
      using vcwla.ennPVs_abg_PVs by simp
    also have "\<dots> = (\<integral>\<^sup>+t\<in>{0.. T x \<xi>}. $v.^t \<partial>(IM cpa.abg))"
      by (rewrite nn_integral_null_delta[OF _ _ sdTx]; simp)
    also have "\<dots> = dcta.ennPV"
      apply (rewrite dcta.ennPV_abg_f_fn)
      by (rewrite Icc_Cont_nn_integral_interval_measure_cong; simp)
    also have "\<dots> = ennreal dcta.PV"
      by (rule dcta.ennPV_PV[OF dcta.ennPV_fin])
    finally have "ennreal (\<integral>t\<in>{0..< T x \<xi>}. $v.^t \<partial>(IM cpa.abg)) = ennreal dcta.PV" .
    hence "(\<integral>t\<in>{0..< T x \<xi>}. $v.^t \<partial>(IM cpa.abg)) = dcta.PV"
      by (rewrite ennreal_inj[THEN sym]; simp add: dcta.PV_nonneg) }

  hence "(\<integral>\<xi>. (\<integral>t\<in>{0..< T x \<xi>}. $v.^t \<partial>(IM cpa.abg)) \<partial>(\<MM> \<downharpoonright> alive x)) =
    (\<integral>\<xi>. annuity.PV i (defer_cont_term_ann.abg 0 (T x \<xi>)) \<partial>(\<MM> \<downharpoonright> alive x))"
    by (intro Bochner_Integration.integral_cong; simp)
  thus ?thesis
    unfolding APV_defer_cont_whole_life_ann_def PV_defer_cont_term_ann_def using vcwla.ennAPV_fin
    by (rewrite vcwla.APV_PV_abg; simp add: that)

qed

end

end
