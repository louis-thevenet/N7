% fonction entrainement_arbre (pour l'exercice 1)

function arbre = entrainement_arbre(X,Y,taille_minimale_feuille)

    arbre = fitctree(X, Y, MinLeafSize=taille_minimale_feuille);

end
