% Fonction estim_param_Dorth_MV (exercice_3.m)

function [theta_Dorth,rho_Dorth] = ...
         estim_param_Dorth_MV(x_donnees_bruitees,y_donnees_bruitees,tirages_theta)


    [x_G, y_G, x_donnees_bruitees_centrees, y_donnees_bruitees_centrees] = centrage_des_donnees(x_donnees_bruitees,y_donnees_bruitees);

    residus_Dyx = (x_donnees_bruitees_centrees.* cos(tirages_theta) + y_donnees_bruitees_centrees .* sin(tirages_theta));
    [~, Indice] = min(sum(residus_Dyx.*residus_Dyx));
    theta_Dorth = tirages_theta(Indice);
    rho_Dorth = x_G * cos(theta_Dorth) + y_G * sin(theta_Dorth);
end