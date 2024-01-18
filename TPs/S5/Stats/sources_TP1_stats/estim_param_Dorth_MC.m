% Fonction estim_param_Dorth_MC (exercice_4.m)

function [theta_Dorth,rho_Dorth] = ...
                 estim_param_Dorth_MC(x_donnees_bruitees,y_donnees_bruitees)

[x_G, y_G, x_donnees_bruitees_centrees, y_donnees_bruitees_centrees] = centrage_des_donnees(x_donnees_bruitees,y_donnees_bruitees);


C = [x_donnees_bruitees_centrees y_donnees_bruitees_centrees];
[V,D] = eig(C'*C);
[~,Indice] = min(diag(D));
Y_p = V(Indice,:)';

theta_Dorth = atan(Y_p(2,1) / Y_p(1,1));
rho_Dorth = x_G * cos(theta_Dorth) + y_G * sin(theta_Dorth);
end