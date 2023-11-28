clear;
close all;
clc;

load donnees_exercice_1;

%------------------------------------------------------------------------------------------
% Classification de l'ensemble d'apprentissage par maximum de vraisemblance
%------------------------------------------------------------------------------------------

% Grille de classification par maximum de vraisemblance entre les 2 classes :
Y_pred_MV_grille = classification_MV(X_grille,mu_1,Sigma_1,mu_2,Sigma_2); % FONCTION A CODER
Y_pred_MV_grille = reshape(Y_pred_MV_grille,length(graduation_carac_2),length(graduation_carac_1));

% Affichage de la grille du maximum de vraisemblance :
figure('Name','Classification par maximum de vraisemblance',...
       'Position',[0.02*L,0.1*H,0.47*L,0.7*H],...
       'Color',[0.7 0.75 0.85]);
    imagesc(graduation_carac_1,graduation_carac_2,Y_pred_MV_grille)
    carte_couleurs = [0.5 0.5 1; 1 0.5 0.5];
    colormap(carte_couleurs);
    axis xy;
    axis(limites_affichage);
    xlabel(nom_carac_1);
    ylabel(nom_carac_2);
    set(gca,'FontSize',20);
    hold on;

% Calcul des bonnes classifications dans l'ensemble d'apprentissage :
Y_app_pred_MV = classification_MV(X_app,mu_1,Sigma_1,mu_2,Sigma_2); % FONCTION A CODER
[pourcentage_bonne_classification_MV, pourcentage_bonne_classification_fibrome, ...
 pourcentage_bonne_classification_melanome] = qualite_classification(Y_app_pred_MV,Y_app); % FONCTION A CODER

% Affichage des points de l'ensemble d'apprentissage :
    [f_ok,m_ok] = affichage_points_classes(X_app,Y_app,Y_app_pred_MV);

% Affichage du taux de bonnes classifications :
    title({'Classification par MV (apprentissage)' ...
           [num2str(pourcentage_bonne_classification_MV,'%.1f') '% de bonnes classifications']});
    legend([f_ok,m_ok],...
           ['Fibromes bien classes (' num2str(pourcentage_bonne_classification_fibrome,'%.1f') '%)'],...
           ['Melanomes bien classes (' num2str(pourcentage_bonne_classification_melanome,'%.1f') '%)'],...
           'Location','NorthWest');
    set(gca,'FontSize',20);
