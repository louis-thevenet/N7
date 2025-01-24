include("../src/newton.jl")
 # votre algorithme de Newton
include("../test/tester_newton.jl") # la fonction pour tester votre algorithme de Newton
#
afficher = true # si true, alors affiche les résultats des algorithmes
#
tester_newton(newton, afficher); # tester l'algorithme de Newton
include("../src/newton.jl") # votre algorithme de Newton
include("../test/fonctions_de_tests.jl") # pour avoir la fonction d'affichage des résultats


println("Test du fichier")

# Fonction f0
# -----------
f0(x) = sin(x)
grad_f0(x) = cos(x) # la gradient de la fonction f0
hess_f0(x) = -sin(x) # la hessienne de la fonction f0
solution = -pi/2
x0 = solution
x_sol, f_sol, flag, nb_iters = newton(f0, grad_f0, hess_f0, x0)
afficher_resultats("Newton", "f0", x0, x_sol, f_sol, flag, nb_iters, solution)
x0 = -pi/2+0.5
x_sol, f_sol, flag, nb_iters = newton(f0, grad_f0, hess_f0, x0)
afficher_resultats("Newton", "f0", x0, x_sol, f_sol, flag, nb_iters, solution)
x0 = pi/2
x_sol, f_sol, flag, nb_iters = newton(f0, grad_f0, hess_f0, x0)
afficher_resultats("Newton", "f0", x0, x_sol, f_sol, flag, nb_iters, solution)

############################################
# 1. Les tests unitaires précédents passent 
# 2.


solution = [1.,1.,1.]
x0 = solution
x_sol, f_sol, flag, nb_iters = newton(fct1, grad_fct1, hess_fct1, x0)
afficher_resultats("Newton", "fct1", x0, x_sol, f_sol, flag, nb_iters, solution)
x0 = [200., -330., 0.]
x_sol, f_sol, flag, nb_iters = newton(fct1, grad_fct1, hess_fct1, x0)
afficher_resultats("Newton", "fct1", x0, x_sol, f_sol, flag, nb_iters, solution)
x0 = -[200., -330., 0.]
x_sol, f_sol, flag, nb_iters = newton(fct1, grad_fct1, hess_fct1, x0)
afficher_resultats("Newton", "fct1", x0, x_sol, f_sol, flag, nb_iters, solution)

# 3.


solution = [1.,1.]
x0 = [0.00000000001,1000000000000000.]
x_sol, f_sol, flag, nb_iters = newton(fct2, grad_fct2, hess_fct2, x0)
afficher_resultats("Newton", "fct2", x0, x_sol, f_sol, flag, nb_iters, solution)

