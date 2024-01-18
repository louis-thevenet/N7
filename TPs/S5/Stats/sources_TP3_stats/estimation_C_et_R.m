% Fonction estimation_C_et_R (exercice_3.m)

function [C_estime,R_estime,ecart_moyen] = ...
         estimation_C_et_R(x_donnees_bruitees,y_donnees_bruitees,C_tests,R_tests)



    n_donnees=length(x_donnees_bruitees);
    n_tirages=length(C_tests);

    Mx = repmat(x_donnees_bruitees, 1,n_tirages )- repmat(C_tests(1,:), n_donnees, 1);
    My = repmat(y_donnees_bruitees, 1, n_tirages) -repmat(C_tests(2,:), n_donnees, 1);
    distance = sqrt(Mx.^2-My.^2);
    score = sum((distance - repmat(R_tests, length(x_donnees_bruitees), 1)).^2, 1);
    
    [ecart, indice_min] = min(score);
    C_estime = C_tests(:, indice_min);
    R_estime = R_tests(indice_min);

    ecart_moyen=ecart / n_donnees;
end