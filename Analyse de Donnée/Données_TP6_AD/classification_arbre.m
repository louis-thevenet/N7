% fonction classification_arbre (pour l'exercice 1)

function Y_pred = classification_arbre(arbre,X)

    [Y_pred, ~] = predict(arbre, X);

end
