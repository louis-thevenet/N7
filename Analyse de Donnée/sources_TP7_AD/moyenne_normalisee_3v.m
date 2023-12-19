% fonction moyenne_normalisee_3v (pour l'exercice 1bis)

function x = moyenne_normalisee_3v(I)

    % Conversion en flottants :
    I = single(I);
    
    % Calcul des couleurs normalisees :
    somme_canaux = max(1,sum(I,3));
    r = I(:,:,1)./somme_canaux;
    v = I(:,:,2)./somme_canaux;
    
    % Calcul des couleurs moyennes :
    r_barre = mean(r(:));
    v_barre = mean(v(:));

    moy_contour = 0;
    bord = 5;
    for j=1:size(I, 2)
        for i=1:bord
            moy_contour = moy_contour + r(i, j) + r(end-i, j);
        end
    end

    for i=2:size(I, 1)-1
        for j=1:bord
            moy_contour = moy_contour + r(i, j) + r(i, end-j);
        end
    end
    moy_contour = moy_contour / (bord*(size(I, 1) *2 + (size(I, 2)-2)*2));

    moy_centrale = 0;
    i_centre = round(size(I, 1)/2);
    j_centre = round(size(I, 2)/2);
    cnt = 0;
    rayon=0.1 *max(size(I,1), size(I,2));
    for i=1:size(I,1)
        for j=1:size(I,2)
                if (i-i_centre)^2 + (j-j_centre)^2 < rayon^2
                    cnt=cnt+1;
                    moy_centrale = moy_centrale + I(i,j, 1);
                end
        end
    end
    moy_centrale = moy_centrale / (cnt );
    x = [r_barre v_barre (moy_contour-moy_centrale)];

end



