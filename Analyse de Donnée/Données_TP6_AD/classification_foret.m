% fonction classification_foret (pour l'exercice 2)

function Y_pred = classification_foret(foret, X)

    Y_pred_tmp = zeros(length(X), length(foret));
    for i = 1:length(foret)
        Y_pred_tmp(:, i) = classification_arbre(foret{i},X);
    end

    Y_pred = mode(Y_pred_tmp, 2);
end
