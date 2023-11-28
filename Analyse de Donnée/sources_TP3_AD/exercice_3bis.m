clear;
close all;
clc;

exercice_2;
load donnees_exercice_3;

%------------------------------------------------------------------------------------------
% Classification de l'ensemble d'apprentissage par maximum a posteriori
%------------------------------------------------------------------------------------------

% Grille de classification par maximum a posteriori entre les 2 classes :
Y_pred_MAP_grille = classification_MAP(X_grille,p1_max,mu_1,Sigma_1,mu_2,Sigma_2); % FONCTION A CODER
Y_pred_MAP_grille = reshape(Y_pred_MAP_grille,length(graduation_carac_2),length(graduation_carac_1));

% Affichage de la grille du maximum a posteriori :
figure('Name','Classification par maximum a posteriori',...
       'Position',[0.51*L,0.1*H,0.47*L,0.7*H],...
       'Color',[0.7 0.75 0.85]);
    imagesc(graduation_carac_1,graduation_carac_2,Y_pred_MAP_grille)
    carte_couleurs = [0.5 0.5 1; 1 0.5 0.5];
    colormap(carte_couleurs);
    axis xy;
    axis(limites_affichage);
    title(['Classification par MAP avec p_1 = ' num2str(p1_max,'%.2f') ' (apprentissage)']);
    xlabel(nom_carac_1);
    ylabel(nom_carac_2);
    set(gca,'FontSize',20);
    hold on;
    
% Calcul des bonnes classifications dans l'ensemble d'apprentissage :
Y_app_pred_MAP = classification_MAP(X_app,p1_max,mu_1,Sigma_1,mu_2,Sigma_2); % FONCTION A CODER
[pourcentage_bonne_classification_MAP, pourcentage_bonne_classification_fibrome, ...
 pourcentage_bonne_classification_melanome] = qualite_classification(Y_app_pred_MAP,Y_app); % FONCTION A CODER

% Affichage des points de l'ensemble d'apprentissage :
    [f_ok,m_ok] = affichage_points_classes(X_app,Y_app,Y_app_pred_MAP);

% Affichage du taux de bonnes classifications :
    title({['Classification par MAP avec p_1 = ' num2str(p1_max,'%.2f') ' (apprentissage)'] ...
	      [num2str(pourcentage_bonne_classification_MAP,'%.1f') '% de bonnes classifications']});
    legend([f_ok,m_ok],...
           ['Fibromes bien classes (' num2str(pourcentage_bonne_classification_fibrome,'%.1f') '%)'],...
           ['Melanomes bien classes (' num2str(pourcentage_bonne_classification_melanome,'%.1f') '%)'],...
           'Location','NorthWest');
    set(gca,'FontSize',20);
