% fonction moyenne_normalisee_2v (pour l'exercice 1)

function x = moyenne_normalisee_2v(I)

    % Conversion en flottants :
    I = single(I);
    
    % Calcul des couleurs normalisees :
    somme_canaux = max(1,sum(I,3));
    r = I(:,:,1)./somme_canaux;
    v = I(:,:,2)./somme_canaux;
    
    % Calcul des couleurs moyennes :
    r_barre = mean(r(:));
    v_barre = mean(v(:));
    x = [r_barre v_barre];

end
