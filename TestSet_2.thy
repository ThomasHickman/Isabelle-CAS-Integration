theory TestSet_2
  imports
    "ODE_Solve_Keyword"
begin

declare [[SODE_solver = "fricas"]]



(*Make these start at line 11, to make it easier to see what test we're looking at*)
ode_solve_thm "λ (t::real) x. (x + t)"
ode_solve_thm "λ (t::real) x. tan t" "{t. cos t > 0}"
ode_solve_thm "λ (t::real) x. x^2"
ode_solve_thm "λ (t::real) (x,y). (-y,x)"
ode_solve_thm "λ (t::real) x. 1/t"
ode_solve_thm "λ (t::real) x. 1/(2*x-1)" "{t. t> 0}" UNIV "x > 0" (*Failure in the Isabelle tactic, can be solved if powr_half_sqrt is present*)
ode_solve_thm "λ (t::real) (x,y). (x*y, 3)"
ode_solve_thm "λ (t::real) (x,y). (2*x+y, x)" (*fricas produces the wrong answer*)
ode_solve_thm "λ (t::real) (x,y). (2*x+y+t^2, x)" (*fricas produces the wrong answer*)
ode_solve_thm "λ (t::real) x. arcsin t" "{- 1<..<1}" (* failure in ode_cert to do fractions properly - need to prove ‹x * inverse (sqrt (1 - x⇧2)) = sqrt(1 - x * x) * x / (1 - x * x)›*)
ode_solve_thm "λ (t::real) x. sqrt t" "{0<..}"
ode_solve_thm "λ (t::real) x. t powr (1/5)" "{0<..}"
ode_solve_thm "λ (t::real) x. t powr (sqrt 2)" "{0<..}" (* failure in ode_cert to do fractions properly*)
ode_solve_thm "λ (t::real) (x,y,z). (x+y, y+2*z, x^2+1)" "{0<..}" (* fricas can't do this *)
ode_solve_thm "λ (t::real) x. x^2 - t" (* Bessel function - we're not going to solve this *)
ode_solve_thm "λ (t::real) (x,y). (y, exp(t^2))" (* Imaginary error function - we're not going to solve this *)
ode_solve_thm "λ (t::real) x. sin x / ln x" (* Unsolvable SODE *)
ode_solve_thm "λ (t::real) (x,y). (ln t, x)"

declare [[SODE_solver = "wolfram"]]

ode_solve_thm "λ (t::real) x. (x + t)"
ode_solve_thm "λ (t::real) x. tan t" "{t. cos t > 0}"
ode_solve_thm "λ (t::real) x. x^2"
ode_solve_thm "λ (t::real) (x,y). (-y,x)"
ode_solve_thm "λ (t::real) x. 1/t"
ode_solve_thm "λ (t::real) x. 1/(2*x-1)" "{t. t> 0}" UNIV "x > 0" (*Failure in the Isabelle tactic*)
ode_solve_thm "λ (t::real) (x,y). (x*y, 3)"
ode_solve_thm "λ (t::real) (x,y). (2*x+y, x)" (*wolfram produces the wrong answer - looks like it generates an approximation*)
ode_solve_thm "λ (t::real) (x,y). (2*x+y+t^2, x)" (*wolfram produces the wrong answer - looks like it generates an approximation*)
ode_solve_thm "λ (t::real) x. arcsin t" "{- 1<..<1}" (* failure in ode_cert to do fractions properly*)
ode_solve_thm "λ (t::real) x. sqrt t" "{0<..}"
ode_solve_thm "λ (t::real) x. t powr (1/5)" "{0<..}"
ode_solve_thm "λ (t::real) x. t powr (sqrt 2)" "{0<..}" (* failure in ode_cert to do fractions properly*)
ode_solve_thm "λ (t::real) (x,y,z). (x+y, y+2*z, x^2+1)" "{0<..}" (* Failure in translation *)
ode_solve_thm "λ (t::real) x. x^2 - t" (* Bessel function - we're not going to solve this *)
ode_solve_thm "λ (t::real) (x,y). (y, exp(t^2))" (* Imaginary error function - we're not going to solve this *)
ode_solve_thm "λ (t::real) x. sin x / ln x" (* Unsolvable SODE *)
ode_solve_thm "λ (t::real) (x,y). (ln t, x)"
end

