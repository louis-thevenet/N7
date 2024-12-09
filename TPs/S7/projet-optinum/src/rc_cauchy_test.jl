include("../src/regions_de_confiance.jl")
include("../test/tester_rc_cauchy.jl")
#
afficher = true # si true, alors affiche les résultats des algorithmes
#
tester_rc_cauchy(regions_de_confiance,afficher);
