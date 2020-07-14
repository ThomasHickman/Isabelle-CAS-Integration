import operator
import re
import sys
from random import randint
import itertools
import warnings

from sage.all_cmdline import *
import sage.functions.all as Fn
import sage.symbolic.operators as Ops
from sage.symbolic.function import SymbolicFunction

from sympy.calculus.util import continuous_domain
from sympy.sets import ImageSet, Integers, Naturals, Naturals0
from sympy import Q, S, Union, ask, assuming

def assert_equals(a, b):
    assert a == b, str(a) + " != " + str(b)

infix_mappings = {
    Ops.add_vararg: (' + ', 1),
    operator.add: (' + ', 1),
    operator.sub: (' - ', 1),
    Ops.mul_vararg: (' * ', 2),
    operator.mul: (' * ', 2),
    operator.truediv: ('/', 2),
    operator.pow: ("powr", 3) # NOTE: integer powers are handled differently
}

fn_mappings = {
    Fn.sin: "sin",
    Fn.cos: "cos",
    Fn.sec: "sec",
    Fn.csc: "csc",
    Fn.cot: "cot",
    Fn.tan: "tan",
    Fn.arcsin: "arcsin",
    Fn.arccos: "arccos",
    Fn.arctan: "arctan",
    Fn.erf: "erf",
    sage.functions.other.Function_abs(): "abs",
    Fn.arccot: "arccot",
    Fn.arccsc: "arccsc",
    Fn.arcsec: "arcsec",

    Fn.tanh: "tanh",
    Fn.sinh: "sinh",
    Fn.cosh: "cosh",
    Fn.coth: "coth",
    Fn.sech: "sech",
    Fn.csch: "csch",
    Fn.arcsinh: "arcsinh",
    Fn.arccosh: "arccosh",
    Fn.arctanh: "arctanh",
    Fn.arccoth: "arccoth",
    Fn.arcsech: "arcsech",
    Fn.arccsch: "arccsch",

    Fn.ln: "ln",
    Fn.exp: "exp",
}

def reconstantify(terms):
    consts = set(itertools.chain(*(term.variables() for term in terms))).difference(set(dVars + [iVar] + free_vars))
    for i, const in enumerate(consts):
        for termI, term in enumerate(terms):
            terms[termI] = term.subs(const == var("C" + str(i)))

existing_stubs = []
def stubify(term):
    """
    Replaces all constants in `term` with "C" + a random number, in order to prevent 
    constant collisions
    """
    global existing_stubs

    consts = set(term.variables()).difference(set(dVars + [iVar] + free_vars + existing_stubs + [newD]))
    for i, const in enumerate(consts):
        stub = var("s_" + str(randint(0, 100000)))
        existing_stubs.append(stub)

        term = term.subs(const == stub)
    return term

def solve_indep(eqs, i_var, d_vars):
    """
    In SODES with $dx/dt=f(x, t)$ (this is only a function of the independent variable and dependent
    variable), solve $dx/dt$ as an ODE and substitute into the rest of the equations.

    @returns (solutions, equations_yet_to_be_solved)
    """
    sols = []
    new_eqs = []
    while True:
        for eq in eqs:
            eq_vars = set(eq.rhs().variables())
            rhs = eq.rhs()
            curr_d_var = eq.lhs().operator().function()(i_var)
            if any((not bool(d_var == curr_d_var) and rhs.has(d_var) for d_var in d_vars)):
                new_eqs.append(eq)
            else:
                de_sol = my_desolve(eq, curr_d_var, ivar=i_var)
                sols.append(curr_d_var == de_sol)
        
        if len(eqs) == len(new_eqs):
            return (sols, new_eqs)
        else:
            for i, eq in enumerate(new_eqs):
                new_eqs[i] = eq.subs(sols)
            eqs = new_eqs
            new_eqs = []

def test_solve_indep():
    t = var('t', domain='real')
    xt, yt, zt = function('x')(t), function('y')(t), function('z')(t)

    assert_equals(
        str(solve_indep([diff(xt, t) == xt * yt, diff(yt, t) == t], t, [xt, yt])),
        "([y(t) == 1/2*t^2 + c1, x(t) == c2*e^(1/6*t^3 + c1*t)], [])"
    )

    assert_equals(
        str(solve_indep([diff(xt, t) == 2*yt+zt, diff(zt, t) == t*xt, diff(yt, t) == t], t, [xt, yt, zt])),
        "([y(t) == 1/2*t^2 + c1], [diff(x(t), t) == t^2 + 2*c1 + z(t), diff(z(t), t) == t*x(t)])"
    )

def replace_wt_higher_deriv(eqs, i_var, d_vars):
    """
    In SODEs which have equations of the form $dx/dt=y$, replaces $y$ with $dx/dt$.
    :returns: (ODEs which have been subsituted in, ODEs of the form above)
    """
    simple_odes, other_odes = [], []
    for eq in eqs:
        if eq.rhs() in d_vars and eq.lhs().operator().function()(i_var) != eq.rhs():
            simple_odes.append(eq)
        else:
            other_odes.append(eq)
    
    for i, eq in enumerate(other_odes):
        while True:
            ode_before = other_odes[i]

            for simple_ode in simple_odes:
                other_odes[i] = other_odes[i].substitute_function(
                    simple_ode.rhs().operator(), simple_ode.lhs().function())

            if ode_before == other_odes[i]:
                break

    return (other_odes, simple_odes)

def test_replace_wt_higher_deriv():
    t = var('t', domain='real')
    xt, yt, zt = function('x')(t), function('y')(t), function('z')(t)

    assert_equals(
        str(replace_wt_higher_deriv([diff(xt, t) == yt, diff(yt, t) == zt, diff(zt, t) == 2], t, [xt, yt, zt])),
        "([diff(x(t), t, t, t) == 2], [diff(x(t), t) == y(t), diff(y(t), t) == z(t)])"
    )

def decode_symbol(sym):
    if sym.endswith("_SBL"):
        return "\<" + sym[:-4] + ">"
    else:
        return sym

def exprToIsabelle(expr):
    if isinstance(expr, sage.rings.rational.Rational):
        return str(expr)
    elif expr.is_numeric():
        if expr.is_real():
            return str(expr)
        else:
            raise NotImplementedError("Conversion of complex number is not implemented")
    elif expr == pi:
        return "pi"
    elif expr == e:
        return "exp(1)"
    elif expr.is_symbol():
        return "(" + decode_symbol(str(expr)) + " :: real)"
    else:
        op = expr.operator()
        opands = expr.operands()
        opands_strs = []
        for opand in opands:
            opand_str = exprToIsabelle(opand)
            opand_operator = opand.operator()
            if opand.is_numeric() and not opand.is_integer():
                opand_operator = operator.truediv

            if  op in infix_mappings and \
                opand_operator in infix_mappings and \
                infix_mappings[opand_operator][1] < infix_mappings[op][1]:

                opand_str = "(" + opand_str + ")"

            opands_strs.append(opand_str)

        if op == operator.pow:
            if re.fullmatch("[0-9]+", opands_strs[1]) != None:
                return "^".join(opands_strs)
            # if re.fullmatch("[0-9/()]+", opands_strs[1]) != None:
            #     num = eval(opands_strs[1])

            #     if int(num - 0.5) == int(num - 0.5):
            #         return "sqrt(" + opands_strs[0] + ")" +\
            #             ("" if num == 0.5 else "*" + opands_strs[0] + ("" if num == 1.5 else "^" + str(int(num - 0.5))))

            return " powr ".join(opands_strs)
        if op in infix_mappings:
            return infix_mappings[op][0].join(opands_strs)
        elif op in fn_mappings:
            return fn_mappings[op] + "(" + ",".join(opands_strs) + ")"
        elif op == iVar or op in [dVar.operator() for dVar in dVars]:
            return op.name() + "(" + ",".join(opands_strs) + ")"
        else:
            raise Exception("Cannot parse expression: " + str(expr))

def find_real_domain(f, symbol):
    from sympy import symbols
    try:
        # We first need to make sure all variables are registered as being real, before
        # we pass into continuous_domain, as the Sage conversion doesn't preserved Reals.
        for sym in f.free_symbols.difference({symbol}):
            f = f.subs(sym, symbols(str(sym), real=True))

        new_symbol = symbols(str(symbol), real=True)
        f = f.subs(symbol, new_symbol)
        symbol = new_symbol

        return continuous_domain(f, symbol, S.Reals)
    except Exception:
        warnings.warn("Failed to find the domain of: " + str(f), RuntimeWarning)
        raise
        return S.Reals

def test_find_real_domain():
    from sympy.abc import t as my_t
    from sympy import Union, Interval, oo, Intersection, Abs
    assert_equals(find_real_domain(1/my_t, my_t), Union(Interval.open(-oo, 0), Interval.open(0, oo)))
    assert_equals(find_real_domain(Abs(my_t), my_t), S.Reals)

def sympy_condition_to_isabelle(cond):
    from sympy.core import relational as Re
    relations_map = {
        Re.Eq: " = ",
        Re.Ne: " \<noteq> ",
        Re.Lt: " < ",
        Re.Le: " \<le> ",
        Re.Gt: " > ",
        Re.Ge: " \<ge> ",
    }

    if isinstance(cond, Re.Relational):
        return exprToIsabelle(cond.lhs._sage_()) + relations_map[type(cond)] +\
            exprToIsabelle(cond.rhs._sage_())
    else:
        raise RuntimeError("Cannot convert SymPy condition: " + str(cond))

def sympy_range_to_isabelle(rng):
    from sympy import oo
    from sympy.sets import (Interval, Union, Intersection, Complement, ImageSet, Integers, 
        Naturals, Naturals0, FiniteSet, ConditionSet)
    if isinstance(rng, Interval):
        left_bit = ""
        if rng.left != -oo:
            left_bit = "(" + str(rng.left) + ")"
            if rng.left_open:
                left_bit += "<"

        right_bit = ""
        if rng.right != oo:
            right_bit = "(" + str(rng.right) + ")"
            if rng.right_open:
                right_bit = "<" + right_bit

        if left_bit == "" and right_bit == "":
            return "UNIV"

        return "{" + left_bit + ".." + right_bit + "}"
    elif isinstance(rng, Union):
        return " \<union> ".join((sympy_range_to_isabelle(arg) for arg in rng.args))
    elif isinstance(rng, Intersection):
        return " \<inter> ".join((sympy_range_to_isabelle(arg) for arg in rng.args))
    elif isinstance(rng, Complement):
        return " - ".join((sympy_range_to_isabelle(arg) for arg in rng.args))
    elif isinstance(rng, ImageSet):
        # TODO: handle the case when we have more than two variables which are called the same
        # thing, and are dummies (we need to do some renaming).
        assert len(rng.lamda.variables) == 1
        p_vars = rng.lamda.variables
        return "{" + exprToIsabelle(rng.lamda.expr._sage_()) + \
            "|" + " ".join([p_var.name for p_var in p_vars]) + ". " + \
            "\<and>".join([x[0].name + " \<in> " + sympy_range_to_isabelle(x[1]) for x in zip(p_vars, rng.args[1:])]) + \
            "}"
    elif isinstance(rng, FiniteSet):
        return "{" + ", ".join((exprToIsabelle(x._sage_()) for x in rng)) + "}"
    elif isinstance(rng, ConditionSet):
        return "{" + str(rng.sym) + " \<in> " + sympy_range_to_isabelle(rng.base_set) + ". " + \
             sympy_condition_to_isabelle(rng.condition) + "}"
    elif rng == Integers:
        return "Ints"
    elif rng == Naturals0:
        return "Nats"
    elif rng == Naturals:
        return "(Nats - {0})"
    else:
        raise RuntimeError("Cannot convert: '" + str(rng) + "' of type: '" + str(type(rng)) + "'")

def test_sympy_range_to_isabelle():
    from sympy import Dummy, ImageSet, Lambda, S, pi
    from sympy.sets import Interval
    _n = Dummy("n")

    assert_equals(sympy_range_to_isabelle(ImageSet(Lambda(_n, 2*_n*pi + pi/2), S.Integers)), "{pi*1/2+pi*n*2|n. n \<in> Ints}")

    assert_equals(sympy_range_to_isabelle(Interval.Lopen(1, 2)), "{1<..2}")
    assert_equals(sympy_range_to_isabelle(S.Reals), "UNIV")

def get_solution_domain(sols, iVar):
    from sympy import Union, Interval, oo, Intersection, Abs
    sIVar = iVar._sympy_()
    domain = S.Reals
    for sol in sols:
        domain = Intersection(domain, find_real_domain(sol.rhs()._sympy_(), sIVar))

    return domain


def test():
    gs = list(globals().keys())
    for g_name in gs:
        if g_name.startswith("test_") and callable(globals()[g_name]):
            print(g_name)
            globals()[g_name]()

def preprocess_and_solve(odes, i_var, d_vars):
    """
    Preprocesses the ode inputs with `replace_wt_higher_deriv` and `solve_indep`, and then solves.
    :returns: an array of the solved equations, in the order of the variables in d_vars.
    """
    wodes, subs_odes = replace_wt_higher_deriv(odes, i_var, d_vars)
    sols, wodes = solve_indep(wodes, i_var, d_vars)

    if wodes != []:
        sols.append(my_desolve_system(wodes, d_vars, ivar=i_var))

    for sub_ode in subs_odes:
        sols.append(
            sub_ode.rhs() == sub_ode.lhs().operator().function()(i_var).subs(sols).diff(i_var))

    return [d_var == d_var.subs(sols) for d_var in d_vars]

def extract_full_solution(de_sol, dvar, ivar):
    if de_sol == "failed":
        raise RuntimeError("Failed to find the solution to the SODE")

    if de_sol.operator() == operator.eq or de_sol.has(dvar):
        new_sols = [stubify(sol.rhs()) for sol in solve(de_sol, dvar) if not sol.has(I)]
        if new_sols == []:
            raise RuntimeError("Cannot solve the equation: '" + str(de_sol) + "' in terms of " + str(dvar))

        return new_sols
    else:
        return [stubify(de_sol)]

# NOTE: for both of the functions below: Sage's FriCAS integration doesn't like equations to contain
# a variable "D" (as it clashes with the differential operator), so we have to do some renaming beforehand. 
newD = var("newD68151")

def my_desolve(ode, dvar, ivar, *args, **kwargs):
    if ODE_solver == "sympy":
        from sympy import dsolve
        sol = dsolve(ode._sympy_(), dvar._sympy_())

        if isinstance(sol, list):
            sol = sol[0]

        return sol._sage_().rhs()

    var("D")
    if "D" in [str(x) for x in ode.variables()]:
        ode, dvar, ivar = [x.subs(D == newD) for x in (ode, dvar, ivar)]

    de_sol = desolve(ode, dvar, *args, ivar=ivar, algorithm=ODE_solver, **kwargs)
    return extract_full_solution(de_sol, dvar, ivar)[0].subs(newD == D)

def my_desolve_system(sode, dvars, ivar, *args, **kwargs):
    if SODE_solver == "sympy":
        from sympy import dsolve
        sols = dsolve([ode._sympy_() for ode in sode], dvars)

        return [sol._sage_() for sol in sols[:len(sode)]]


    from itertools import product as cart_product
    var("D")

    for ode, dvar, i in zip(odes, dvars, range(len(odes))):
        if "D" in [str(x) for x in ode.variables()]:
            odes[i], dvar, ivar = [x.subs(D == newD) for x in (ode, dvar, ivar)]

    de_sols = desolve_system(sode, dvars, *args, ivar=ivar, algorithm=SODE_solver, **kwargs)
    # NOTE: at the moment, desolve_system never returns a value that we need to solve for, so
    # we're not using extract_full_solution
    #list(cart_product(new_sols))[0]
    #new_sols = [extract_full_solution(sol, dvars[i], ivar) for i, sol in enumerate(de_sols)]

    return [de_sol.subs(newD == D) for de_sol in de_sols]

if len(sys.argv) == 2 and sys.argv[1] == "-t":
    test()
else:
    # The input is a python fragment, which when executed yeilds a variable called "sol" containing
    # the solved equation
    exec(sys.argv[1])
    if preprocess_SODEs:
        sols = preprocess_and_solve(odes, iVar, dVars)
    else:
        sols = my_desolve_system(odes, dVars, ivar=iVar)

    reconstantify(sols)

    print("\<lambda> " + str(iVar) + ".("  + ", ".join([
        exprToIsabelle(sol.rhs()) for sol in sols]) + ")")
    print(sympy_range_to_isabelle(get_solution_domain(sols, iVar)))
