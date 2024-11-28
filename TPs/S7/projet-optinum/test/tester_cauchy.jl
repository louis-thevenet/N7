# Ecrire les tests de l'algorithme du pas de Cauchy
using Test
include("../test/fonctions_de_tests.jl")

function tester_cauchy(cauchy::Function, afficher::Bool)

    println("Affichage des résultats des algorithmes : ", afficher, "\n")

    # Tolérance utilisé dans les tests
    tol_test = 1e-3

    Test.@testset "algorithme du Pas de Cauchy" begin
            # Cas nul
            @test [0;0] ≈ cauchy([0;0], [7 0;0 2], 1,tol_abs=tol_test)

            # Cas H définie positive, pas de cauchy dans la région de confiance
            @test -[1/6;1/3] ≈ cauchy([0.5;1], [7 0;0 2], 1,tol_abs=tol_test)

            # Cas H définie positive, pas de cauchy pas dans la région de confiance
            @test [-0.044721359549995794, -0.08944271909999159] ≈ cauchy([0.5;1], [7 0;0 2], 0.1,tol_abs=tol_test)

            # Cas H non définie positive
            @test [-1;0] ≈ cauchy([10;0], -[7 0;0 2], 1,tol_abs=tol_test)
        end

    end
