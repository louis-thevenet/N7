using LinearAlgebra
"""
Approximation d'une solution du problème min f(x), x ∈ Rⁿ, en utilisant l'algorithme de Newton.

# Syntaxe

   x_sol, f_sol, flag, nb_iters, xs = newton(f, gradf, hessf, x0; kwargs...)

# Entrées

   - f       : (Function) la fonction à minimiser
   - gradf   : (Function) le gradient de la fonction f
   - hessf   : (Function) la Hessienne de la fonction f
   - x0      : (Union{Real,Vector{<:Real}}) itéré initial
   - kwargs  : les options sous formes d'arguments "keywords"
      • max_iter : (Integer) le nombre maximal d'iterations (optionnel, par défaut 1000)
      • tol_abs  : (Real) la tolérence absolue (optionnel, par défaut 1e-10)
      • tol_rel  : (Real) la tolérence relative (optionnel, par défaut 1e-8)
      • epsilon  : (Real) le epsilon pour les tests de stagnation (optionnel, par défaut 1)

# Sorties

   - x_sol : (Union{Real,Vector{<:Real}}) une approximation de la solution du problème
   - f_sol : (Real) f(x_sol)
   - flag  : (Integer) indique le critère sur lequel le programme s'est arrêté
      • 0  : convergence
      • 1  : stagnation du xk
      • 2  : stagnation du f
      • 3  : nombre maximal d'itération dépassé
   - nb_iters : (Integer) le nombre d'itérations faites par le programme
   - xs    : (Vector{Vector{<:Real}}) les itérés

# Exemple d'appel

   f(x)=100*(x[2]-x[1]^2)^2+(1-x[1])^2
   gradf(x)=[-400*x[1]*(x[2]-x[1]^2)-2*(1-x[1]) ; 200*(x[2]-x[1]^2)]
   hessf(x)=[-400*(x[2]-3*x[1]^2)+2  -400*x[1];-400*x[1]  200]
   x0 = [1; 0]
   x_sol, f_sol, flag, nb_iters, xs = newton(f, gradf, hessf, x0, max_iter=10)

"""
function newton(f::Function, gradf::Function, hessf::Function, x0::Union{Real,Vector{<:Real}}; 
    max_iter::Integer = 1000, 
    tol_abs::Real = 1e-10, 
    tol_rel::Real = 1e-8, 
    epsilon::Real = 1)

    #
 
    x_sol = x0
    f_sol = f(x_sol)
    flag  = -1
    nb_iters = 0
    xs = [x0] # vous pouvez faire xs = vcat(xs, [xk]) pour concaténer les valeurs

   norm_f_x0 = norm(gradf(x0))

   if norm(gradf(x0)) <= max(tol_rel * norm(norm_f_x0), tol_abs)
      return x_sol, f_sol, 0, nb_iters, xs
   end

   while true
      xk=x_sol
      dk = hessf(xk) \ (-gradf(xk))
      xkp1 = xk + dk
      xs = vcat(xs, [xkp1]) 
      nb_iters = nb_iters + 1

      x_sol = xkp1
      f_sol = f(x_sol)

      if norm(gradf(xkp1)) <= max(tol_rel * norm(norm_f_x0), tol_abs)
         return x_sol, f_sol, 0, nb_iters, xs

      elseif norm(xkp1 - xk) <= epsilon * max(tol_rel * norm(xk), tol_abs)
         return x_sol, f_sol, 1, nb_iters, xs

      elseif norm(f(xkp1) - f(xk)) <= epsilon * max(tol_rel * norm(f(xk)), tol_abs)
         return x_sol, f_sol, 2, nb_iters, xs

      elseif nb_iters >= max_iter
         return x_sol, f_sol, 3, nb_iters, xs
      end
   end

   return x_sol, f_sol, 0, nb_iters, xs # devrait pas atteindre ça
end
