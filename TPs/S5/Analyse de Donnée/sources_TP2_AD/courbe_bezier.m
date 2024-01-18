% fonction courbe_bezier (pour exercice_1.m)

function y = courbe_bezier(x,parametres)

    % Degre de la courbe de Bezier
    d = length(parametres)-1;

    % Initialisation de y par beta_0*B_0^d(x) pour toutes les courbes
    y = parametres(1)*vecteur_bernstein(x,d,0);

    for k = 1:d
        % Ajout des termes beta_k^i(x)*B_k^d(x)
        % (decalage a k+1 pour parametre car il y a beta_0 au debut)
        y = y + parametres(k+1)*vecteur_bernstein(x,d,k);
    end

end
