using Test

"""
Tester l'algorithme du gient conjugué tronqué

# Les cas de test (dans l'ordre)

    - la quadratique 1
    - la quadratique 2
    - la quadratique 3
    - la quadratique 4
    - la quadratique 5
    - la quadratique 6
    
"""
function tester_gct(gct::Function)

    # Tolérance utilisé dans les tests
    tol_test = 1e-3

    Test.@testset "Gradient conjugué tronqué" begin
        # le cas de test 1
        g = [0 ; 0]
        H = [7 0 ; 0 2]
        Δ = 1
        s = gct(g,H,Δ)
        Test.@test  s ≈ [0.0 ; 0.0] atol = tol_test

        # le cas de test 2 H definie positive
        g = [6 ; 2]
        H = [7 0 ; 0 2]
        Δ = 0.5       # sol = pas de Cauchy  
        s = gct(g,H,Δ)
        Test.@test  s ≈ -Δ*g/norm(g) atol = tol_test
        Δ = 1.2       # saturation à la 2ieme itération  
        s = gct(g,H,Δ)
        Test.@test  s ≈ [-0.8740776099190263, -0.8221850958502244] atol = tol_test
        Δ = 3         # sol = min global  
        s = gct(g,H,Δ)
        Test.@test  s ≈ -H\g atol = tol_test

        # le cas test 2 bis matrice avec 1 vp < 0 et 1 vp > 0
        g = [1,2]
        H = [1 0 ; 0 -1]
        Δ = 1.       # g^T H g < 0 première direction concave
        s = gct(g,H,Δ)
        Test.@test  s ≈ -Δ*g/norm(g) atol = tol_test
        g = [1,0]
        Δ = 0.5       #  g^T H g > 0 sol pas de Cauchy
        s = gct(g,H,Δ)
        Test.@test  s ≈ -Δ*g/norm(g) atol = tol_test
        g = [2,1]        #  g^T H g > 0 sol à l'itération 2, saturation
        Δ = 6
        s = gct(g,H,Δ)
        Test.@test  isapprox(s, [0.48997991959774634, 5.979959839195494], atol = tol_test) || isapprox(s, [-4.489979919597747, -3.979959839195493], atol = tol_test)

        # le cas de test 5
        g = [2 ; 3]
        H = [4 6 ; 6 5]
        Δ = 3
        s = gct(g,H,Δ)
        Test.@test  s ≈ [1.9059020876695578 ; -2.3167946029410595] atol = tol_test

        # le cas de test 6
        # Le pas de Cauchy conduit à un gient nul en 1 itération
        g = [2 ; 0]
        H = [4 0 ; 0 -15]
        Δ = 2
        s = gct(g,H,Δ)
        Test.@test  s ≈ [-0.5 ; 0.0] atol = tol_test
    end
end
