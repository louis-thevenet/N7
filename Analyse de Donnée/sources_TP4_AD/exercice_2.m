clear;
close all;
clc;

% Parametres pour l'affichage des donnees :
taille_ecran = get(0,'ScreenSize');
L = taille_ecran(3);
H = taille_ecran(4);

%--------------------------------------------------------------------------
% Calcul des parametres du SVM sur les donnees d'apprentissage
%--------------------------------------------------------------------------

% Donnees non filtrees :
load donnees_carac;
X_app = X_app(:,1:2);
X_test = X_test(:,1:2);
Y_app(Y_app == 2) = -1; % Changement du label pour utiliser le SVM
Y_test(Y_test == 2) = -1; % Changement du label pour utiliser le SVM
nb_donnees_app = size(X_app,1);
nb_donnees_test = size(X_test,1);

% Estimation du SVM avec noyau gaussien :
nb_classes = 2;
vecteur_sigma = 0.001:0.0001:0.02; % Ecart-type du noyau gaussien

% Recherche du parametre sigma optimal :
[pourcentage_meilleur_classification_SVM_test, sigma_opt_test, ...
 vecteur_pourcentages_bonnes_classifications_SVM_app, ...
 vecteur_pourcentages_bonnes_classifications_SVM_test] = ...
maximisation_classification_SVM_noyau(X_app,Y_app,X_test,Y_test,vecteur_sigma); % FONCTION A CODER

%--------------------------------------------------------------------------
% Affichage des courbes d'optimisation de l'hyperparametre sigma
%--------------------------------------------------------------------------

figure('Name','Classification par SVM avec noyau gaussien (optimisation)',...
       'Position',[0.1*L,0.1*H,0.8*L,0.7*H],...
       'Color',[0.7 0.75 0.85]);
    plot(vecteur_sigma,vecteur_pourcentages_bonnes_classifications_SVM_app,'LineWidth',2)
    hold on
    plot(vecteur_sigma,vecteur_pourcentages_bonnes_classifications_SVM_test,'LineWidth',2)
    plot(sigma_opt_test,pourcentage_meilleur_classification_SVM_test,'m+','MarkerSize',10,'LineWidth',3);
    xlim([vecteur_sigma(1) vecteur_sigma(end)])
    ylim([60 100])
    grid on
    
    title(['Maximum de classification des donnees de test = ' ...
           num2str(pourcentage_meilleur_classification_SVM_test,'%.1f') '%' ...
           ' pour \sigma^* = ' num2str(sigma_opt_test,'%.3f')])
    xlabel('\sigma')
    ylabel('% de bonnes classifications')
    legend('Apprentissage','Test','\sigma^*')
    set(gca,'FontSize',20);

save hyperparametre_exercice_2 sigma_opt_test;
