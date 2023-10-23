% Fonction ensemble_E_recursif (exercie_1.m)

function [E,contour,G_somme] = ensemble_E_recursif(E,contour,G_somme,i,j,...
                                                   voisins,G_x,G_y,card_max,cos_alpha)
    contour(i,j) =0;

        for k=1:1:size(voisins,1)
            v = voisins(k,:)+[i,j];
            i_voisin = v(1);
            j_voisin = v(2);
            if contour(i_voisin,j_voisin)==1
                G_v = [G_x(i_voisin, j_voisin),G_y(i_voisin,j_voisin)];
   
                if ((G_v/norm(G_v)) * (G_somme' / norm(G_somme)) >= cos_alpha)
                    E=[E;v];
                    G_somme=G_somme+G_v;
                    [E, contour, G_somme]= ensemble_E_recursif(E,contour,G_somme, ...
                        i_voisin, j_voisin, voisins,G_x, G_y,card_max, cos_alpha);
                end
            end
        end
end
  
