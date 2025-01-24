using Test
include("../test/fonctions_de_tests.jl")

"""
Tester l'algorithme du lagrangien augmenté

# Entrées

	- afficher : (Bool) affichage ou non des résultats de chaque test

# Les cas de test (dans l'ordre)

	- Newton 
    	• fct1 : x01, x02
	  	• fct2 : x03, x04
  	- gct
      	• fct1 : x01, x02
	  	• fct2 : x03, x04
	- Cauchy
		• fct1 : x01, x02
    	• fct2 : x03, x04

"""
function tester_lagrangien_augmente(LA::Function, afficher::Bool)

    println("Affichage des résultats des algorithmes : ", afficher, "\n")

	# La tolérance utilisée dans les tests
	tol_erreur = 1e-4

	# initialisation des paramètres
	tol = 1e-5 # tol_abs et tol_rel
	
	# Les trois algorithmes d'optimisations sans contraintes utlisés
	algos = ["newton", "rc-cauchy", "rc-gct"]

	#
	f1 = fct1; gf1 = grad_fct1; Hf1 = hess_fct1; c1 = contrainte1; gc1 = grad_contrainte1; Hc1 = hess_contrainte1
	f2 = fct2; gf2 = grad_fct2; Hf2 = hess_fct2; c2 = contrainte2; gc2 = grad_contrainte2; Hc2 = hess_contrainte2
	x01 = pts2.x01
	x02 = pts2.x02
	x03 = pts2.x03
	x04 = pts2.x04

	Test.@testset "Lagrangien augmenté  " begin 	

		Test.@testset "Avec $algo" for algo in algos

			# le cas de test 1
			x0 = x01
			x_sol, f_sol, flag, nb_iters, _ = LA(f1, gf1, Hf1, c1, gc1, Hc1, x0, tol_abs=tol, tol_rel=tol, algo_noc=algo)
			if (afficher)
				afficher_resultats("LA et " * algo, "f1", x0, x_sol, f_sol, flag, nb_iters, sol_fct1_augm)
			end
			Test.@test x_sol ≈ sol_fct1_augm atol=tol_erreur

			# le cas de test 2
			x0 = x02
			x_sol, f_sol, flag, nb_iters, _ = LA(f1, gf1, Hf1, c1, gc1, Hc1, x0, tol_abs=tol, tol_rel=tol, algo_noc=algo)
			if (afficher)
				afficher_resultats("LA et " * algo, "f1", x0, x_sol, f_sol, flag, nb_iters, sol_fct1_augm)
			end
			Test.@test x_sol ≈ sol_fct1_augm atol=tol_erreur

			# le cas de test 3
			x0 = x03
			x_sol, f_sol, flag, nb_iters, _ = LA(f2, gf2, Hf2, c2, gc2, Hc2, x0, tol_abs=tol, tol_rel=tol, algo_noc=algo)
			if (afficher)
				afficher_resultats("LA et " * algo, "f2", x0, x_sol, f_sol, flag, nb_iters, sol_fct2_augm)
			end
			Test.@test x_sol ≈ sol_fct2_augm atol=tol_erreur

			# le cas de test 4
			x0 = x04
			x_sol, f_sol, flag, nb_iters, _ = LA(f2, gf2, Hf2, c2, gc2, Hc2, x0, tol_abs=tol, tol_rel=tol, algo_noc=algo)
			if (afficher)
				afficher_resultats("LA et " * algo, "f2", x0, x_sol, f_sol, flag, nb_iters, sol_fct2_augm)
			end
			Test.@test x_sol ≈ sol_fct2_augm atol=tol_erreur

		end

	end

end
