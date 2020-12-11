theory ODE_extra
  imports 
    Derivative_extra
    "Ordinary_Differential_Equations.ODE_Analysis"
begin

subsection \<open> ODE Tactics \<close>

text \<open> \emph{ode\_cert} is a simple tactic for certifying solutions to systems of differential equations \<close>

declare cos_gt_zero_pi[field_simps]
declare Orderings.order_class.dual_order.strict_implies_not_eq[field_simps]
declare tan_def[field_simps]
declare sqrt_def[field_simps]
declare root_powr_inverse[field_simps]
declare powr_mult_base[field_simps]

method ode_cert = (rule_tac solves_odeI, simp_all add: has_vderiv_on_def, safe intro!:
    has_vector_derivative_Pair, (rule has_vector_derivative_eq_rhs, (rule derivative_intros; (simp add: field_simps)?)+,
      ((simp add: field_simps)+)?)+)

type_synonym 'c ODE = "real \<Rightarrow> 'c \<Rightarrow> 'c"

text \<open> A simple example is the following system of ODEs for an objecting accelerating according to gravity. \<close>

abbreviation "grav \<equiv> 9.81"

abbreviation grav_ode :: "(real \<times> real) ODE" where
"grav_ode \<equiv> (\<lambda> t (v, h). (- grav, v))"

text \<open> We also present the following solution to the system of ODEs, which is a function from 
  initial values of the continuous variables to a continuous function that shows how the variables 
  change with time. \<close>

abbreviation grav_sol :: "real \<times> real \<Rightarrow> real \<Rightarrow>  real \<times> real" where
"grav_sol \<equiv> \<lambda> (v\<^sub>0, h\<^sub>0)  \<tau>. (v\<^sub>0 - grav * \<tau>, v\<^sub>0 * \<tau> - grav * (\<tau> * \<tau>) / 2 + h\<^sub>0)"

text \<open> Finally, we show how this solution to the ODEs can be certified. \<close>

lemma 
  "(grav_sol (v\<^sub>0, h\<^sub>0) solves_ode grav_ode) T UNIV"
  by ode_cert

text \<open> More examples \<close>

lemma "((\<lambda> t. exp t) solves_ode (\<lambda> t y. y)) T UNIV"
  by ode_cert

lemma "((\<lambda> t. (cos t, sin t)) solves_ode (\<lambda> t (x, y). (-y, x))) T UNIV"
  by ode_cert

text \<open>Thomas' work:\<close>

lemma real_type_to_set[simp]: "(x::real) \<in> Reals" by (simp add: Reals_def)

abbreviation "sec x == 1/cos x"
abbreviation "csc x == 1/sin x"
abbreviation "coth x == 1/tanh(x)"
abbreviation "sech x == 1/cosh(x)"
abbreviation "csch x == 1/sinh(x)"
abbreviation "arccsc x == arcsin(1/x)"
abbreviation "arccot x == pi/2 - arctan x"
abbreviation "arcsec x == arccos(1/x)"
abbreviation "arcsinh x == ln(x +  sqrt(x^2 + 1))"
abbreviation "arccosh x == ln(x +  sqrt(x^2 - 1))"
abbreviation "arctanh x == ln((1 + x)/(1 - x))"
abbreviation "arccoth x == ln((x + 1)/(x - 1))"
abbreviation "arcsech x == ln((1 + sqrt(1 - x^2))/x)"
abbreviation "arccsch x == ln(x +  sqrt(x^2 + 1))"

end