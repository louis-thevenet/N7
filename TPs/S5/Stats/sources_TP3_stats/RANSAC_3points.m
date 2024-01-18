% Fonction RANSAC_3points (exercice_3)

function [C_estime,R_estime] = RANSAC_3points(x_donnees_bruitees,y_donnees_bruitees,parametres)

    % Parametres de l'algorithme RANSAC :
    S_ecart = parametres(1); % seuil pour l'ecart
    S_prop = parametres(2); % seuil pour la proportion
    k_max = parametres(3); % nombre d'iterations
    n_tirages = parametres(4); 
    n_donnees = size(x_donnees_bruitees,1);
    ecart_moyen_min = Inf;

    [G, R_moyen, ~] = calcul_G_et_R_moyen(x_donnees_bruitees,y_donnees_bruitees);
    [C_tests,R_tests] = tirages_aleatoires_uniformes(n_tirages,G,R_moyen);

    for i =1:k_max
        Indices = randperm(length(C_tests),2);
        [C_estime_k,R_estime_k,ecart_moyen] = estimation_C_et_R(x_donnees_bruitees,y_donnees_bruitees,C_tests(:, Indices),R_tests(Indices));

        Distances = abs(sqrt((x_donnees_bruitees-C_estime_k(1)).^2 + (y_donnees_bruitees -C_estime_k(2)).^2) - R_estime_k);
        
        Distances=Distances(Distances < S_ecart);
        if length(Distances)/n_donnees > S_prop && ecart_moyen_min> ecart_moyen 
            ecart_moyen_min=ecart_moyen;
            C_estime=C_estime_k;
            R_estime=R_estime_k;
        end


    end

    %[C_3p,R_3p] = estim_param_cercle_3points(x,y)
end