theory manually_solved_cases
  imports
    ODE_Solve_Keyword
begin

(* This solves \<open>ode_solve_thm "\<lambda> (t::real) x. tan t" "{t. cos t > 0}"\<close>*)
lemma "((\<lambda>t. C0 + ln (inverse (((tan t)\<^sup>2 + 1) ^ 1)) * - 1 / 2) solves_ode (\<lambda>t x. tan t)) {t. 0 < cos t} \<real>"
  apply ode_cert
proof -
  fix x :: real
  have f1: "\<And>r ra. (r::real) - - ra = ra - - r"
    by simp
  have f2: "\<And>r ra rb. (r::real) * ra - - (rb * ra) = (r - - rb) * ra"
    by (metis diff_minus_eq_add distrib_right)
  have f3: "\<And>r ra. (r::real) * (r * ra) = r\<^sup>2 * ra"
    by (simp add: power2_eq_square)
  have "cos x * ((sin x - - sin x) * (((cos x)\<^sup>2)\<^sup>2 * ((sin x)\<^sup>2 - - (cos x)\<^sup>2))) = cos x * ((sin x - - sin x) * ((cos x)\<^sup>2)\<^sup>2)"
    by simp
  then have "cos x * (cos x * (cos x * (cos x * (cos x * (cos x * (cos x * (sin x - - sin x)) - - (sin x * (sin x * (sin x - - sin x)))))))) = cos x * (cos x * (cos x * (cos x * (cos x * (sin x - - sin x)))))"
    using f3 f2 f1 by (metis (no_types) mult.commute mult.left_commute)
  then show "cos x * (cos x * (cos x * (cos x * (cos x * (cos x * (cos x * (sin x * 2))))))) + cos x * (cos x * (cos x * (cos x * (cos x * (sin x * (sin x * (sin x * 2))))))) = cos x * (cos x * (cos x * (cos x * (cos x * (sin x * 2)))))"
    by (simp add: distrib_left)
qed


(* This solves \<open>ode_cert "\<lambda> (t::real) x. 1/(2*x-1)" "{t. t> 0}"\<close>*)
lemma "((\<lambda> t.((t :: real) * arcsin(t) + (C0::real) + (t^2 * -1 + 1) powr (1/2))) solves_ode (\<lambda>t x. arcsin t)) {-1<..<1} \<real>"
  apply ode_cert
   apply (smt mult_less_cancel_right2 mult_minus_left)
  apply simp
proof -
  have "\<And>x. - 1 < x \<and> x < 1 \<Longrightarrow> x * inverse (sqrt (1 - x\<^sup>2)) = (1 - x * x) powr (1 / 2) * x / ( abs(1 - x * x) )"
    apply (simp add: power2_eq_square powr_half_sqrt square_le_1)
    apply (smt divide_inverse power2_eq_square powr_half_sqrt real_divide_square_eq real_sqrt_mult_self square_le_1)
    done
  thus "\<And>x. - 1 < x \<and> x < 1 \<Longrightarrow> x * inverse (sqrt (1 - x\<^sup>2)) = (1 - x * x) powr (1 / 2) * x / (1 - x * x)"
    by (smt power2_eq_square square_le_1)
qed

(*This solves \<open>ode_cert "\<lambda> (t::real) x. t powr (sqrt 2)" "{0<..}"\<close>*)
theorem "((\<lambda>t. 2 powr (1 / 2) * (t :: real) * t powr 2 powr (1 / 2) * inverse ((2 powr (1 / 2) + 2) ^ 1) +(C0 :: real)) solves_ode (\<lambda>t x. t powr sqrt 2)) {0<..} \<real>"
  apply ode_cert
    apply (smt powr_gt_zero)
   apply (rule has_vector_derivative_eq_rhs)
    apply (rule derivative_intros; (simp add: field_simps)?)+
   apply (simp add: field_simps)+ 
  apply (simp add: powr_half_sqrt)
  apply (metis add.commute add_pos_pos distrib_right less_numeral_extra(3) mult.commute nonzero_mult_div_cancel_right real_sqrt_gt_0_iff zero_less_numeral)
  done
  
end