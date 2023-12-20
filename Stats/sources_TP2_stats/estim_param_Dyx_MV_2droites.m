% Fonction estim_param_Dyx_MV_2droites (exercice_2.m) 

function [a_Dyx_1,b_Dyx_1,a_Dyx_2,b_Dyx_2] = ... 
         estim_param_Dyx_MV_2droites(x_donnees_bruitees,y_donnees_bruitees,sigma, ...
                                     tirages_G_1,tirages_psi_1,tirages_G_2,tirages_psi_2)    
    

    residus_Dyx1 = (y_donnees_bruitees - tirages_G_1(2, :) -repmat(tan(tirages_psi_1), size(x_donnees_bruitees)).*(x_donnees_bruitees-tirages_G_1(1, :)));
    residus_Dyx2 = (y_donnees_bruitees - tirages_G_2(2, :) -repmat(tan(tirages_psi_2), size(x_donnees_bruitees)) .* (x_donnees_bruitees-tirages_G_2(1, :)));

    [~,Indice] = max(sum(log(exp(-residus_Dyx1.^2 / (2*sigma.^2)) + exp(-residus_Dyx2.^2 / (2*sigma.^2)))));

    a_Dyx_1 = tan(tirages_psi_1(Indice));
    b_Dyx_1 = tirages_G_1(2, Indice)-a_Dyx_1*tirages_G_1(1, Indice);


    a_Dyx_2 = tan(tirages_psi_2(Indice));
    b_Dyx_2 = tirages_G_2(2, Indice )-a_Dyx_2*tirages_G_2(1, Indice);

end