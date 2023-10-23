% Fonction matrice_inertie (exercice_2.m)

function [M_inertie,C] = matrice_inertie(E,G_norme_E) 

    pi = sum(G_norme_E);
    x_moy = G_norme_E * E(1,:)' ./ pi;
    y_moy = G_norme_E * E(2,:)' ./ pi;
    cov=sum(G_norme_E .* (E(1,:)-x_moy) .* (E(2,:)-y_moy)) / pi;

    M_inertie=[x_moy, cov; cov, y_moy];
    C = [x_moy, y_moy];

end