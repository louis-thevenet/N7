# Ecrire les tests de l'algorithme du pas de Cauchy
using Test
include("../test/fonctions_de_tests.jl")

function tester_cauchy(cauchy::Function, afficher::Bool)

    println("Affichage des résultats des algorithmes : ", afficher, "\n")

        # tolérance pour les tests


    Test.@testset "algorithme du Pas de Cauchy" begin
            g = [0; 0]
            H = [7 0 ; 0 2]
            delta= 1
            tol_abs= sqrt(eps())
            Test.@testset "test f1 : x0 = solution" begin
                s = cauchy(g, H, delta,tol_abs=tol_abs  )
                if (afficher)
                    println("cauchy", "f1", s)
            end
            Test.@testset "solution" begin
                Test.@test s≈ [0.0, 0.0] 
            end
        end


            # x0 = pi/2
            # g = [cos(x0) ]
            # H = [-sin(x0);]
            # solution = [-pi/2]

            # delta= 2*pi
            # tol_abs= sqrt(eps())
            # Test.@testset "test sinus: x0 = solution" begin
            #     s = cauchy(g, H, delta)
            #     if (afficher)
            #         println("cauchy", "f1", s)
            # end
            # Test.@testset "solution" begin
            #     Test.@test s≈ solution 
            # end
        # end
    end
end
