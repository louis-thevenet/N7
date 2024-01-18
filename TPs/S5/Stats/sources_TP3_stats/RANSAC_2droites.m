% Fonction RANSAC_2droites (exercice_2.m)

function [rho_F_estime,theta_F_estime] = RANSAC_2droites(rho,theta,parametres)

    % Parametres de l'algorithme RANSAC :
    S_ecart = parametres(1); % seuil pour l'ecart
    S_prop = parametres(2); % seuil pour la proportion
    k_max = parametres(3); % nombre d'iterations
    n_donnees = length(rho);
    ecart_moyen_min = Inf;

    for i =1:k_max
        Indices = randperm(length(rho),2);
        [rho_F_k,theta_F_k,ecart_moyen] = estim_param_F(rho(Indices), theta(Indices));
        Distances = abs(rho - rho_F_k*cos(theta-theta_F_k));
        Distances=Distances(Distances < S_ecart);
        if length(Distances)/n_donnees > S_prop && ecart_moyen_min> ecart_moyen 
            ecart_moyen_min=ecart_moyen;
            rho_F_estime=rho_F_k;
            theta_F_estime=theta_F_k;
        end


    end

end