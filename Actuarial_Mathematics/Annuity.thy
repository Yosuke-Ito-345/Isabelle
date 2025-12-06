theory Annuity
  imports "Wlog.Wlog" "Lebesgue_Stieltjes_Integral.Lebesgue_Stieltjes_Integral" Interest 
begin

text \<open>
  In this theory, I describe various kinds of annuities certain in a uniform way.
  I will also use this formulation to introduce life annuities.
\<close>

abbreviation "IM \<equiv> interval_measure"

locale annuity = interest +
  fixes f::real and
    \<comment> \<open>\<open>f\<close> represents the deferred period (possibly \<open>0\<close>).\<close>
    abg :: "real \<Rightarrow> real"
    \<comment> \<open>"abg" stands for "accumulated benefit of guaranteed period annuity"\<close>
    \<comment> \<open>The value abg(\<open>t\<close>) represents the total amount of benefits
        to be paid at or before the time \<open>t\<close>.\<close>
  assumes f_nonneg[simp]: "f \<ge> 0" and
    abg_f_0[simp]: "\<And>t. t < f \<Longrightarrow> abg t = 0" and
    abg_right_continuous[simp]: "\<And>t. continuous (at_right t) abg" and
    abg_mono[simp]: "mono abg"
begin

definition "PV \<equiv> \<integral>t. $v.^t \<partial>(IM abg)"
  \<comment> \<open>present value of the annuity certain\<close>
  \<comment> \<open>When the integral diverges, this definition is interpreted as meaningless.\<close>

definition "ennPV \<equiv> \<integral>\<^sup>+t. $v.^t \<partial>(IM abg)"

lemma abg_measurable[measurable]: "abg \<in> borel_measurable borel"
  using abg_mono borel_measurable_mono by simp

lemma abg_constant_on_f:"abg constant_on {..<f}"
  using abg_f_0 by (simp add: constant_on_def)

lemma PV_nonneg: "PV \<ge> 0"
  unfolding PV_def by (rule Bochner_Integration.integral_nonneg)+ simp

lemma ennPV_PV:
  assumes "ennPV < \<infinity>"
  shows "ennPV = ennreal PV"
  using assms unfolding ennPV_def PV_def apply (rewrite nn_integral_eq_integral)
  by (intro integrableI_bounded) simp_all

end

subsection \<open>Deferred Continuous Perpetual Annuity\<close>

locale defer_cont_perp_ann = interest +
  fixes f::real
  assumes f_nonneg[simp]: "f \<ge> 0"
begin

definition abg :: "real \<Rightarrow> real" where "abg t \<equiv> max (t - f) 0"

lemma abg_f_0[simp]:
  fixes t::real
  assumes "t < f"
  shows "abg t = 0"
  unfolding abg_def using assms by simp

corollary abg_constant_on_f: "abg constant_on {..<f}"
  unfolding constant_on_def by (rule exI[of _ 0]) simp

lemma abg_continuous[simp]:
  fixes t::real
  shows "isCont abg t"
  unfolding abg_def by (simp add: continuous_max)

corollary
  fixes t::real
  shows abg_right_continuous[simp]: "continuous (at_right t) abg" and
    abg_left_continuous[simp]: "continuous (at_left t) abg"
  by (simp add: continuous_at_imp_continuous_within)+

lemma abg_mono[simp]: "mono abg"
  unfolding abg_def by (simp add: monoI)

end

sublocale defer_cont_perp_ann \<subseteq> annuity i f abg
  by (standard; simp)

context defer_cont_perp_ann
begin

lemma DERIV_abg:
  fixes t::real
  assumes "f < t"
  shows "DERIV abg t :> 1"
proof -
  have "DERIV (\<lambda>s. s - f) t :> 1 - 0" by (intro derivative_intros)
  moreover have "\<forall>\<^sub>F s in nhds t. abg s = s - f"
    apply (rewrite eventually_nhds_metric)
    by (rule exI[of _ "t-f"], auto simp add: assms abg_def dist_real_def)
  ultimately show "DERIV abg t :> 1" by (rewrite DERIV_cong_ev; simp)
qed

corollary abg_differentiable_on_f: "abg differentiable_on {f<..}"
  by (meson DERIV_abg differentiable_at_withinI differentiable_on_def
      greaterThan_iff real_differentiable_def)

corollary deriv_abg:
  fixes t::real
  assumes "f < t"
  shows "deriv abg t = 1"
  using assms DERIV_abg DERIV_imp_deriv by blast

lemma set_nn_integral_interval_measure_abg:
  fixes g :: "real \<Rightarrow> real" and A :: "real set"
  assumes "g \<in> borel_measurable borel" and
    A_borel: "A \<in> sets borel" "A \<subseteq> {f..}"
  shows "(\<integral>\<^sup>+t\<in>A. g t \<partial>(IM abg)) = (\<integral>\<^sup>+t\<in>A. g t \<partial>lborel)"
proof -

  wlog A_f: "A \<subseteq> {f<..}" generalizing A keeping A_borel
  proof -
    from assms negation have fA: "f \<in> A" using dual_order.strict_iff_order by auto
    hence "(\<integral>\<^sup>+t\<in>A. g t \<partial>(IM abg)) = (\<integral>\<^sup>+t\<in>{f}. g t \<partial>(IM abg)) + (\<integral>\<^sup>+t\<in>A-{f}. g t \<partial>(IM abg))"
      using assms by (rewrite nn_integral_disjoint_pair[THEN sym]; simp add: insert_absorb)
    also have "\<dots> = (\<integral>\<^sup>+t\<in>A-{f}. g t \<partial>lborel)"
    proof -
      have "(\<integral>\<^sup>+t\<in>{f}. g t \<partial>(IM abg)) = 0" using interval_measure_singleton_continuous by simp
      moreover have "(\<integral>\<^sup>+t\<in>A-{f}. g t \<partial>(IM abg)) = (\<integral>\<^sup>+t\<in>A-{f}. g t \<partial>lborel)"
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
    have "(\<integral>\<^sup>+t\<in>A. g t \<partial>(IM abg)) = (\<integral>\<^sup>+t\<in>A. ennreal (g t) * ennreal (deriv abg t) \<partial>lborel)"
      using assms A_borel A_f abg_differentiable_on_f deriv_abg
      by (rewrite set_nn_integral_interval_measure_deriv[of abg f \<infinity>]; simp)
    also have "\<dots> = (\<integral>\<^sup>+t\<in>A. g t \<partial>lborel)"
      apply (intro set_nn_integral_cong)
      using deriv_abg A_f by force+
    finally show ?thesis .
  qed

qed

lemma
  assumes "i > 0"
  shows PV_set_integrable: "set_integrable lborel {f..} (\<lambda>t. $v.^t)" and
    PV_calc: "PV = (LBINT t:{f..}. $v.^t)"
proof -

  text \<open>Proof of "PV_set_integrable"\<close>
  show PV_set_integrable: "set_integrable lborel {f..} (\<lambda>t. $v.^t)"
    using assms set_integrable_powr_Ici v_lt_1_iff_i_pos v_pos by presburger

  text \<open>Proof of "PV_calc"\<close>
  have "ennPV = (\<integral>\<^sup>+t\<in>{f..}. $v.^t \<partial>(IM abg))"
    unfolding ennPV_def using abg_constant_on_f by (rewrite nn_integral_interval_measure_Ici; simp)
  also have "\<dots> = (\<integral>\<^sup>+t\<in>{f..}. $v.^t \<partial>lborel)"
    by (rewrite set_nn_integral_interval_measure_abg; simp)
  also have "\<dots> = ennreal (LBINT t:{f..}. $v.^t)"
    by (rule set_nn_integral_eq_set_integral; simp add: PV_nonneg PV_set_integrable)
  finally have "ennPV = ennreal (LBINT t:{f..}. $v.^t)" .
  thus "PV = (LBINT t:{f..}. $v.^t)" using ennreal_inj ennPV_PV PV_nonneg by simp

qed

end

context interest
begin

definition PV_defer_cont_perp_ann :: "real \<Rightarrow> real" (\<open>$a'''_{_\<bar>\<infinity>\<rceil>}\<close> [0] 200)
  where "$a'_{f\<bar>\<infinity>\<rceil>} \<equiv> annuity.PV i (defer_cont_perp_ann.abg f)"

abbreviation PV_cont_perp_ann :: real (\<open>$a'''_\<infinity>\<rceil>\<close> 200) where "$a'_\<infinity>\<rceil> \<equiv> $a'_{0\<bar>\<infinity>\<rceil>}"

proposition
  a'_defer_perp_set_integrable: "set_integrable lborel {f..} (\<lambda>t. $v.^t)" and
  a'_defer_perp_calc: "$a'_{f\<bar>\<infinity>\<rceil>} = (LBINT t:{f..}. $v.^t)"
  if "f \<ge> 0" "i > 0" for f::real
proof -
  have [simp]: "defer_cont_perp_ann i f"
    apply (intro defer_cont_perp_ann.intro, simp add: interest_axioms)
    using that by (intro defer_cont_perp_ann_axioms.intro) simp
  show "set_integrable lborel {f..} (\<lambda>t. $v.^t)"
    by (rule defer_cont_perp_ann.PV_set_integrable; simp add: that)
  show "$a'_{f\<bar>\<infinity>\<rceil>} = (LBINT t:{f..}. $v.^t)"
    unfolding PV_defer_cont_perp_ann_def using that
    by (rewrite defer_cont_perp_ann.PV_calc; simp)
qed

proposition a'_perp_calc: "$a'_\<infinity>\<rceil> = (LBINT t:{0..}. $v.^t)" if "i > 0"
  using that a'_defer_perp_calc by simp

end

end
