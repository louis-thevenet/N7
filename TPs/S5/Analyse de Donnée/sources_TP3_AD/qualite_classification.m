% fonction qualite_classification (pour l'exercice 2)

function [pourcentage_bonnes_classifications_total,pourcentage_bonnes_classifications_fibrome, ...
          pourcentage_bonnes_classifications_melanome] = qualite_classification(Y_pred,Y)

pourcentage_bonnes_classifications_fibrome = 100*nnz(Y_pred==1 & Y==1)/sum(Y==1);
pourcentage_bonnes_classifications_melanome = 100*nnz(Y_pred~=1 & Y~=1)/sum(Y~=1);


pourcentage_bonnes_classifications_total = 100*(nnz(Y_pred==1 & Y==1)+nnz(Y_pred~=1 & Y~=1))/size(Y,1);
end