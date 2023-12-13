% fonction maximisation_classification_SVM_noyau (pour l'exercice 2)

function [pourcentage_meilleur_classification_SVM_test, sigma_opt_test, ...
          vecteur_pourcentages_bonnes_classifications_SVM_app, ...
          vecteur_pourcentages_bonnes_classifications_SVM_test] = ...
          maximisation_classification_SVM_noyau(X_app,Y_app,X_test,Y_test,vecteur_sigma)

vecteur_pourcentages_bonnes_classifications_SVM_app = zeros(length(X_app));
vecteur_pourcentages_bonnes_classifications_SVM_test = zeros(length(X_app));


for i=1:length(vecteur_sigma)
    sigma = vecteur_sigma(i);
   [X_VS, Y_VS, alpha_VS, c,code_return] = estim_param_SVM_noyau(X_app, Y_app, sigma);

   if code_return ~=1
    break;
   end
   Y_pred = classification_SVM_avec_noyau(X_app, sigma, X_VS, Y_VS, alpha_VS, c);

    vecteur_pourcentages_bonnes_classifications_SVM_app(i) = 100*(nnz(Y_pred==1 & Y_app == 1)/sum(Y_pred==1));
    vecteur_pourcentages_bonnes_classifications_SVM_test(i) = 100*(nnz(Y_pred==1 & Y_test == 1)/sum(Y_pred==1));


end
[~, Indice]=max(vecteur_pourcentages_bonnes_classifications_SVM_test);
sigma_opt_test=vecteur_sigma(Indice);
pourcentage_meilleur_classification_SVM_test=  vecteur_pourcentages_bonnes_classifications_SVM_test(Indice);
end