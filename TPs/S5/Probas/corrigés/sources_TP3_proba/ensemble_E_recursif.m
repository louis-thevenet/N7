% Fonction ensemble_E_recursif (exercie_1.m)

function [E,contour,G_somme] = ensemble_E_recursif(E,contour,G_somme,i,j,...
                                                   voisins,G_x,G_y,card_max,cos_alpha)
    contour(i,j) = 0;
    coords_voisins = [i j] + voisins;
    k = 1;
    while (k <= length(coords_voisins) && length(E) <= card_max)
        disp(E);
        vk = coords_voisins(k,:);
        ik = vk(1);
        jk = vk(2);
        if contour(ik,jk)
            Gvk_x = G_x(ik,jk);
            Gvk_y = G_y(ik,jk);
            Gk = [Gvk_x Gvk_y];
            if (Gk/norm(Gk) * G_somme'/norm(G_somme) >= cos_alpha)
                [E,contour,G_somme] = ensemble_E_recursif([E;vk],contour,G_somme + G_k,i,j,voisins,G_x,G_y,card_max,cos_alpha);
            end
        end
        [E,contour,G_somme] = ensemble_E_recursif(E,contour,G_somme,i,j,voisins,G_x,G_y,card_max,cos_alpha);
        k = k + 1;
    end
end