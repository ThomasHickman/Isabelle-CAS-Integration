theory TestSet
  imports
    "ODE_Solve_Keyword"
begin

declare [[SODE_solver = "fricas"]]

(*Christian's test set*)

(*test_1*)
ode_solve_thm "\<lambda> t x . x"
(*test_2*)
ode_solve_thm "(\<lambda> t (x,y) . (-y,x))"
(*test_3*)
ode_solve_thm "(\<lambda> t x . sqrt(t))"
(*test_4*)
ode_solve_thm "(\<lambda> t (v, h). (- 9.81, v))"
(*test_5*)
ode_solve_thm "(\<lambda> t (a,v,p) . (0,a,v))"
(*test_7*)
ode_solve_thm "(\<lambda> t (x,y). (t+2, x+3))"
(*test_6*)
ode_solve_thm "(\<lambda> t (px,py,dx,dy,s,\<omega>,a,r). (dx * s,dy * s,\<omega>*dy, -\<omega>*dx, a, a/r, 0, 0))"

ode_solve_thm "\<lambda> t x. x^2 - t"
(*test_8*)
ode_solve_thm "(\<lambda> t (x,y). (y, exp(t^2)))"
(*test_9 - this is a problem*)
ode_solve_thm "(\<lambda> t x. sin(x)/ln(x))"
(*test_10*)
ode_solve_thm "(\<lambda> t (x,y). (ln(t), x))"
(*test_11*)
ode_solve_thm "(\<lambda> t x. (x ^ 2))"

(*Thomas' test set*)

(*Previous dissertation tests:*)

ode_solve_thm "(λ (t::real) (x, y). (sqrt t, 3))" "{1..}"
ode_solve_thm "(λ (t::real) (x, y). (t, x))"
ode_solve_thm "(λ (t::real) (x, y). (t+2, x+3))"
ode_solve_thm "(λ (t::real) (x, y). (-2-t, -x-3))"
ode_solve_thm "(λ (t::real) (x, y). (2*t, 3*x))"
ode_solve_thm "(λ (t::real) (x, y). (t/2, x/3))"
ode_solve_thm "(λ (t::real) (x, y). (2/t, 0))"
ode_solve_thm "(λ (t::real) (x, y). (exp(t), 3))"
ode_solve_thm "(λ (t::real) (x, y). (x, y))"
ode_solve_thm "(λ (t::real) (x, y). (ln t, x))"
ode_solve_thm "(λ (t::real) (x, y). (sin t, 3))"
ode_solve_thm "(λ (t::real) (x, y). (cos t, 3))"
ode_solve_thm "(λ (t::real) (x, y). (sinh t, 3))"
ode_solve_thm "(λ (t::real) (x, y). (cosh t, 3))"

(*My tests:*)

ode_solve_thm "(λ (t::real) (x, y). (1/(2*x-1), 0))"
ode_solve_thm "(λ (t::real) (x, y). (x*y, 3))"
ode_solve_thm "(λ (t::real) (x, y). (2 * x + y + 1 + t^2, x))"
ode_solve_thm "(λ (t::real) (x, y). (tan(t), 1))" "({-pi/2<..<pi/2})"
ode_solve_thm "(λ (t::real) (x, y). (arcsin(t), 1))"
ode_solve_thm "(λ (t::real) (x, y). (t powr (1/4), 1))" "{0<..}"
ode_solve_thm "(λ (t::real) (x, y). (t powr sqrt 2, 1))" "{0<..}"
ode_solve_thm "(λ (t::real) (x, y, z). (x+y, y+2*z,x^2+1))"

end