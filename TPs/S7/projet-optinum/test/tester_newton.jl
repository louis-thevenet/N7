using Test
using LinearAlgebra
include("../test/fonctions_de_tests.jl")

"""
Tester l'algorithme de Newton

# Entrées

    - afficher : (Bool) affichage ou non des résultats de chaque test

# Les cas de test (dans l'ordre)

    - fct 1 : x011, x012
    - fct 2 : x021, x022, x023

"""
function tester_newton(newton::Function, afficher::Bool)

    println("Affichage des résultats des algorithmes : ", afficher, "\n")

    # tolérance pour les tests
    tol_erreur = sqrt(eps())

    # options pour Newton
    max_iter = 100
    tol_abs = sqrt(eps())
    tol_rel = 1e-15
    epsilon = 1.0

    #
    Test.@testset "algorithme de Newton" begin
        Test.@testset "test f1 : x0 = solution" begin
            x_sol, f_sol, flag, nb_iters, _ = newton(fct1, grad_fct1, hess_fct1, sol_exacte_fct1, 
                            max_iter=max_iter, tol_abs=tol_abs, tol_rel=tol_rel, epsilon=epsilon)
            if (afficher)
                afficher_resultats("newton", "f1", sol_exacte_fct1, x_sol, f_sol, flag, nb_iters, sol_exacte_fct1)
            end
            Test.@testset "solution" begin
                Test.@test x_sol ≈ sol_exacte_fct1 atol=tol_erreur
            end
            Test.@testset "itération" begin
                Test.@test nb_iters == 0
            end
            Test.@testset "flag" begin
                Test.@test flag == 0
            end
        end
        Test.@testset "test f1 : x0 = x011" begin
            x_sol, f_sol, flag, nb_iters, _ = newton(fct1, grad_fct1, hess_fct1, pts1.x011,  
                            max_iter=max_iter, tol_abs=tol_abs, tol_rel=tol_rel, epsilon=epsilon)
            if (afficher)
                afficher_resultats("newton", "f1", pts1.x011, x_sol, f_sol, flag, nb_iters, sol_exacte_fct1)
            end
            Test.@testset "solution" begin
                Test.@test x_sol ≈ sol_exacte_fct1 atol=tol_erreur
            end
            Test.@testset "itération" begin
                Test.@test nb_iters == 1
            end
            Test.@testset "flag" begin
                Test.@test flag == 0
            end
        end
        Test.@testset "test f1 : x0 = x012" begin
            x_sol, f_sol, flag, nb_iters, _ = newton(fct1, grad_fct1, hess_fct1, pts1.x012, 
                            max_iter=max_iter, tol_abs=tol_abs, tol_rel=tol_rel, epsilon=epsilon)
            if (afficher)
                afficher_resultats("newton", "f1", pts1.x012, x_sol, f_sol, flag, nb_iters, sol_exacte_fct1)
            end
            Test.@testset "solution" begin
                Test.@test x_sol ≈ sol_exacte_fct1 atol = tol_erreur
            end
            Test.@testset "itération" begin
                Test.@test nb_iters == 1
            end
            Test.@testset "flag" begin
                Test.@test flag == 0
            end
        end
        Test.@testset "test f2 : x0 = x021" begin
            x_sol, f_sol, flag, nb_iters, _ = newton(fct2, grad_fct2, hess_fct2, pts1.x021, 
                            max_iter=max_iter, tol_abs=tol_abs, tol_rel=tol_rel, epsilon=epsilon)
            if (afficher)
                afficher_resultats("newton", "f2", pts1.x021, x_sol, f_sol, flag, nb_iters, sol_exacte_fct2)
            end
            Test.@testset "solution" begin
                Test.@test x_sol ≈ sol_exacte_fct2 atol = tol_erreur
            end
            Test.@testset "itération" begin
                Test.@test nb_iters == 6
            end
            Test.@testset "flag" begin
                Test.@test flag == 0
            end
        end
        Test.@testset "test f2 : x0 = x022" begin
            x_sol, f_sol, flag, nb_iters, _ = newton(fct2, grad_fct2, hess_fct2, pts1.x022, 
                            max_iter=max_iter, tol_abs=tol_abs, tol_rel=tol_rel, epsilon=epsilon)
            if (afficher)
                afficher_resultats("newton", "f2", pts1.x022, x_sol, f_sol, flag, nb_iters, sol_exacte_fct2)
            end
            Test.@testset "solution" begin
                Test.@test x_sol ≈ sol_exacte_fct2 atol = tol_erreur
            end
            Test.@testset "itération" begin
                Test.@test nb_iters == 5
            end
            Test.@testset "flag" begin
                Test.@test flag == 0
            end
        end
        Test.@testset "test f2 : x0 = x023" begin
            x_sol, f_sol, flag, nb_iters, _ = newton(fct2, grad_fct2, hess_fct2, pts1.x023, 
                            max_iter=1, tol_abs=tol_abs, tol_rel=tol_rel, epsilon=epsilon)
            if (afficher)
                afficher_resultats("newton", "f2", pts1.x023, x_sol, f_sol, flag, nb_iters, sol_exacte_fct2)
            end
            Test.@testset "solution" begin
                Test.@test norm(x_sol) > 1e6
            end
            Test.@testset "flag" begin
                Test.@test flag == 3
            end
            Test.@testset "itération" begin
                Test.@test nb_iters == 1
            end
            Test.@testset "exception" begin
                Test.@test_throws SingularException _, _, _, _ = newton(fct2, grad_fct2, hess_fct2, pts1.x023, 
                        max_iter=max_iter, tol_abs=tol_abs, tol_rel=tol_rel, epsilon=epsilon)
            end
        end
    end
end
