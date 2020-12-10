theory TestSet_2
  imports
    "ODE_Solve_Keyword"
begin

declare [[SODE_solver = "wolfram"]]

ode_solve_thm "λ (t::real) x. (x + t)"
ode_solve_thm "λ (t::real) x. tan t"
ode_solve_thm "λ (t::real) x. x^2"
ode_solve_thm "λ (t::real) (x,y). (-y,x)"
ode_solve_thm "λ (t::real) x. 1/t"
ode_solve_thm "λ (t::real) x. 1/(2*x-1)"
ode_solve_thm "λ (t::real) (x,y). (x*y, 3)"
ode_solve_thm "λ (t::real) (x,y). (2*x+y, x)"
ode_solve_thm "λ (t::real) (x,y). (2*x+y+t^2, x)"
ode_solve_thm "λ (t::real) x. arcsin t"
ode_solve_thm "λ (t::real) x. sqrt t"
ode_solve_thm "λ (t::real) x. t powr (1/5)"
ode_solve_thm "λ (t::real) x. t powr (sqrt 2)"
ode_solve_thm "λ (t::real) (x,y,z). (x+y, y+2*z, x^2+1)"
ode_solve_thm "λ (t::real) x. x^2 - t"
ode_solve_thm "λ (t::real) (x,y). (y, exp(t^2))"
ode_solve_thm "λ (t::real) x. sin x / ln x"
ode_solve_thm "λ (t::real) (x,y). (ln t, x)"
end

