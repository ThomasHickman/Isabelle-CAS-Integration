theory Keymaera_tests
  imports
    ODE_Solve_Keyword
begin

declare [[SODE_solver = "fricas"]]

ode_solve_thm "(λ ind (x1, x2, d1, t). (d1, d2, -om*d2, 1))"
ode_solve_thm "(λ ind (dP, ptimer). (-dPv, 0.002))"
ode_solve_thm "(λ ind (qx, qy, fx, fy). ((K * qx / D) * fx, (K * qy / D) * fy, fxp, fyp))"
ode_solve_thm "(λ ind (p, v, t). (v, a, 1 ))"
ode_solve_thm "(λ ind (z, t). (v, 1))"
ode_solve_thm "(λ ind (t). (1))"
ode_solve_thm "(λ ind (x, t). (c+b*(u-x), 1))" UNIV
ode_solve_thm "(λ ind (dP, ptimer). (dPv, 0.002))"
ode_solve_thm "(λ ind (x, t). (a, 1))"
ode_solve_thm "(λ ind (x, v). (v, A))"
ode_solve_thm "(λ ind (z, v). (v, -b))"
ode_solve_thm "(λ ind (x1, v1, xi, t). (v1, a1, -vi, 1))"
ode_solve_thm "(λ ind (qx, qy, fx, fy). (K * fx, K * fy, fxp, fyp))"
ode_solve_thm "(λ ind (z, v, t). (v, -b, 1))"
ode_solve_thm "(λ ind (x, v). (v, g+d * v^2))"
ode_solve_thm "(λ ind (x, y). (1, -d))"
ode_solve_thm "(λ ind (z, v, t). (v, a, 1))"
ode_solve_thm "(λ ind (z). (v))"
ode_solve_thm "(λ ind (qx, qy, fx, fy, t). (K * (fx - g * nx), K * (fy - g * ny), fxp, fyp, 1))"
ode_solve_thm "(λ ind (x, y). (y, -(w^2) * x-2 * d * w * y))"
ode_solve_thm "(λ ind (qx, qy, fx, fy). (0, K * fy, fxp, fyp))"
ode_solve_thm "(λ ind (x, y). (1, 1))"
ode_solve_thm "(λ ind (x, v). (v, a))"
ode_solve_thm "(λ ind (h, v, t). (v, -g, 1))"
ode_solve_thm "(λ ind (x). (x^2+x^4))"
ode_solve_thm "(λ ind (dP). (dPv))"
ode_solve_thm "(λ ind (z, v, t). (v, -a, 1 ))"
ode_solve_thm "(λ ind (x1, x2). (d1, d2))"
ode_solve_thm "(λ ind (y). (-d))"
ode_solve_thm "(λ ind (x, y). ((x-3)^4+y^5, y^2))"
ode_solve_thm "(λ ind (x, v, t). (v, A, 1))"
ode_solve_thm "(λ ind (x1, x2, d1, d2, y1, y2, e1, e2). (d1, d2, -om*d2, om*d1, e1, e2, -om*e2, om*e1))"
ode_solve_thm "(λ ind (x, v, t). (v, a, 1))"
ode_solve_thm "(λ ind (x, y). (1, f))"
ode_solve_thm "(λ ind (qx, qy, fx, fy). (K * fx, 0, fxp, fyp))"
ode_solve_thm "(λ ind (x, t). (v, 1))"
ode_solve_thm "(λ ind (qx, qy, fx, fy). (0, 0, fxp, fyp))"
ode_solve_thm "(λ ind (x, y, vx, vy, t, ts). (vx, vy, ax, ay, 1, 1))"
ode_solve_thm "(λ ind (x1, x2). (d1, d2))"
ode_solve_thm "(λ ind (dP). (-dPv))"
ode_solve_thm "(λ ind (x, vx, t, ts). (vx, ax, 1, 1))"
ode_solve_thm "(λ ind (x). (15 + 1/2*( 10 - x ) ))"
ode_solve_thm "(λ ind (qx, qy, fx, fy). (K * fx, (K * qy / D) * fy, fxp, fyp))"
ode_solve_thm "(λ ind (x1, x2). (v1, v2))"
ode_solve_thm "(λ ind (z, v, t). (v, amax, 1))"
ode_solve_thm "(λ ind (x1). (d1))"
ode_solve_thm "(λ ind (qx, qy, fx, fy). ((K * qx / D) * fx, K * fy, fxp, fyp))"
ode_solve_thm "(λ ind (p, t). (v, 1))"
ode_solve_thm "(λ ind (z, v, t). (v, a, 1 ))"
ode_solve_thm "(λ ind (x, y). (1, -2))"
ode_solve_thm "(λ ind (x, y, vx, vy). (vx, vy, -a * vy, a * vx))"
ode_solve_thm "(λ ind (x1, v1, t). (v1, a1, 1))"
ode_solve_thm "(λ ind (t, tc, x, y). (1, 1, Ux, Uy))"
ode_solve_thm "(λ ind (dtimer, ptimer). (1, 1))"
ode_solve_thm "(λ ind (y1, y2). (e1, e2))"
ode_solve_thm "(λ ind (z, v, t). (v, A, 1))"
ode_solve_thm "(λ ind (x). (10 - x))"
ode_solve_thm "(λ ind (x1, x2, z1, z2, vz1, vz2). (v1, v2, vz1, vz2, a1, a2))"
ode_solve_thm "(λ ind (xf, vf, xl, vl, t). (vf, af, vl, al, 1))"
ode_solve_thm "(λ ind (x). ((x-3)^4+a))"
ode_solve_thm "(λ ind (x, v). (v, -b))"
ode_solve_thm "(λ ind (x, y, t). (cx+b*(u-x), cy+b*(u-y), 1))"
ode_solve_thm "(λ ind (y). (f))"
ode_solve_thm "(λ ind (x, t). (b*(u-x), 1))"
ode_solve_thm "(λ ind (t, p, v). (1, v, a ))"
ode_solve_thm "(λ ind (x, y, t, tc). (Ux, Uy, 1, 1))"
ode_solve_thm "(λ ind (h, v). (v, -g))"
ode_solve_thm "(λ ind (x1, v1, x2, v2, t). (v1, a1, v2, a2, 1))"
ode_solve_thm "(λ ind (x, y). (vx, vy))"

end