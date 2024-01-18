% fonction prediction_kmoyennes (pour l'exercice 1)

function Y_pred = prediction_kmoyennes(X,k)

    Y_pred =kmeans(X,k);

end