% Fonction estimation_C (exercice_2.m)

function C_estime = estimation_C(x_donnees_bruitees,y_donnees_bruitees,tirages_C,R_moyen)
    distance_x_carre = (tirages_C(1, :) - x_donnees_bruitees).^2;    
    distance_y_carre = (tirages_C(2, :) - y_donnees_bruitees).^2;    
    distance=sqrt(distance_x_carre+distance_y_carre);
    V=(distance-R_moyen).^2;
    somme=ones(1, size(V,1))*V;
    [~, Ind_min]=min(somme);
    C_estime=tirages_C(:, Ind_min);
end