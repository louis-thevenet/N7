% Fonction calcul_G_et_R_moyen (exercice_1.m)

function [G, R_moyen, distances] = calcul_G_et_R_moyen(x_donnees_bruitees,y_donnees_bruitees)

    G = [mean(x_donnees_bruitees), mean(y_donnees_bruitees)];
    y_distances = y_donnees_bruitees - G(2);
    x_distances = x_donnees_bruitees - G(1);


    R_moyen = mean(sqrt(y_distances .* y_distances + x_distances .* x_distances));
end