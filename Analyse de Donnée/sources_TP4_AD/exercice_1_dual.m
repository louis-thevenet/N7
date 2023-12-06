clear;
close all;
clc;

exercice_1_primal;

% Parametres pour l'affichage des donnees :
taille_ecran = get(0,'ScreenSize');
L = taille_ecran(3);
H = taille_ecran(4);

% Donnees filtrees :
load donnees_carac_filtrees;
X_app = X_app(:,1:2);
Y_app(Y_app == 2) = -1; % Changement du label pour utiliser le SVM

%--------------------------------------------------------------------------
% Creation de la grille pour l'affichage des classes predites
%--------------------------------------------------------------------------

% Parametres d'affichage :
pas = 0.002;
marge = 0.005;
graduation_carac_1 = min(min(X_app(:,1)))-marge:pas:max(max(X_app(:,1)))+marge;
graduation_carac_2 = min(min(X_app(:,2)))-marge:pas:max(max(X_app(:,2)))+marge;
limites_affichage = [graduation_carac_1(1) graduation_carac_1(end) ...
                     graduation_carac_2(1) graduation_carac_2(end)];
nom_carac_1 = 'Compacite';
nom_carac_2 = 'Contraste';

% Estimation du SVM lineaire (formulation duale) :
[X_VS,w,c,code_retour] = estim_param_SVM_dual(X_app,Y_app);

% Si l'optimisation n'a pas converge :
if code_retour ~= 1
	return;
end

% Regle de decision du SVM :
[grille_carac1,grille_carac2] = meshgrid(graduation_carac_1,graduation_carac_2);
X_grille = [grille_carac1(:),grille_carac2(:)];
Y_pred_grille = classification_SVM(X_grille,w,c);
Y_pred_grille = reshape(Y_pred_grille,length(graduation_carac_2),length(graduation_carac_1));

% Affichage des classes predites par le SVM :
figure('Name','Classification par SVM',...
       'Position',[0.51*L,0.1*H,0.47*L,0.7*H],...
       'Color',[0.7 0.75 0.85]);
    imagesc(graduation_carac_1,graduation_carac_2,Y_pred_grille);
    carte_couleurs = [1 0.5 0.5; 0.5 0.5 1];
    colormap(carte_couleurs);
    axis xy;
    axis(limites_affichage);
    xlabel(nom_carac_1);
    ylabel(nom_carac_2);
    set(gca,'FontSize',20);
    hold on;
	
%--------------------------------------------------------------------------
% Classification et affichage des donnees d'apprentissage
%--------------------------------------------------------------------------

% Calcul des bonnes classifications dans l'ensemble d'apprentissage :
Y_app_pred = classification_SVM(X_app,w,c); % FONCTION A CODER
[pourcentage_bonne_classification, pourcentage_bonne_classification_fibrome, ...
 pourcentage_bonne_classification_melanome] = qualite_classification(Y_app,Y_app_pred); % FONCTION A CODER

% Affichage des points de l'ensemble d'apprentissage :
[f_ok,m_ok] = affichage_points_classes(X_app,Y_app,Y_app_pred);

% Les vecteurs de support sont entoures en noir :
vs = plot(X_VS(:,1),X_VS(:,2),'ko','MarkerSize',20,'LineWidth',3);

title('Donnees separables - SVM avec la forme duale')
legend([f_ok,m_ok,vs],...
       ['Fibromes bien classes (' num2str(pourcentage_bonne_classification_fibrome,'%.1f') '%)'],...
       ['Melanomes bien classes (' num2str(pourcentage_bonne_classification_melanome,'%.1f') '%)'],...
       'Vecteurs supports','Location','NorthWest');
set(gca,'FontSize',20);
