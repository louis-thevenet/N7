include("../src/lagrangien_augmente.jl")
 # votre algorithme de Newton
include("../test/tester_lagrangien_augmente.jl") # la fonction pour tester votre algorithme de Cauchy
#
afficher = true
tester_lagrangien_augmente(lagrangien_augmente, afficher); # tester l'algorithme de Cauchy
