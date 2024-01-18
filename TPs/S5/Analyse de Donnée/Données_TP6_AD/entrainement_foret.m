% fonction entrainement_foret (pour l'exercice 2)

function foret = entrainement_foret(X,Y,nb_arbres,proportion_individus)
    foret = cell(nb_arbres);
    for i=1:nb_arbres
       Indices = randperm(length(X), length(X)* proportion_individus);
       foret{i} = fitctree(X(Indices, :), Y(Indices), NumVariablesToSample=sqrt(length(X)));
    end
        
end
