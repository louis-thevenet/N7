% fonction qualite_classification (pour l'exercice 2)

function [pourcentage_bonnes_classifications_total, ...
          pourcentage_bonnes_classifications_fibrome, ...
          pourcentage_bonnes_classifications_melanome] ...
          = qualite_classification(Y_pred,Y)

    % Pourcentage de fibromes bien classes :
    nb_bonnes_classifications_fibrome = sum(Y == 1 & Y_pred == 1);
    nb_donnees_fibrome = sum(Y == 1);
    pourcentage_bonnes_classifications_fibrome = 100*nb_bonnes_classifications_fibrome/nb_donnees_fibrome;

    % Pourcentage de melanomes bien classes : 
    nb_bonnes_classifications_melanome = sum(Y ~= 1 & Y_pred ~= 1);
    nb_donnees_melanome = sum(Y ~= 1);
    pourcentage_bonnes_classifications_melanome = 100*nb_bonnes_classifications_melanome/nb_donnees_melanome;

    % Pourcentage d'elements bien classes au total :
    nb_bonnes_classifications_total = sum(Y == Y_pred);
    nb_donnees = size(Y,1);
    pourcentage_bonnes_classifications_total = 100*nb_bonnes_classifications_total/nb_donnees;

end