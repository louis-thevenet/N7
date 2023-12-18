clear
close all
clc

% Parametres pour l'affichage des donnees :
taille_ecran = get(0,'ScreenSize');
L = taille_ecran(3);
H = taille_ecran(4);

%--------------------------------------------------------------------------
% Classification avec une foret aleatoire
%--------------------------------------------------------------------------

% Donnees non filtrees :
load donnees_carac;
X_app = X_app(:,1:2);
X_test = X_test(:,1:2);
Y_app(Y_app == 2) = -1; % Changement du label pour utiliser le SVM
Y_test(Y_test == 2) = -1; % Changement du label pour utiliser le SVM
nb_donnees_app = size(X_app,1);
nb_donnees_test = size(X_test,1);

% Entrainement de la foret aleatoire :
nb_arbres = 200;
proportion_individus = 0.8;
foret = entrainement_foret(X_app, Y_app, nb_arbres, proportion_individus); % FONCTION A CODER
% Classification des donnees d'apprentissage
Y_app_pred = classification_foret(foret,X_app); % FONCTION A CODER
[pourcentage_bonne_classification_app_opt, pourcentage_bonne_classification_app_fibrome_opt, ...
 pourcentage_bonne_classification_app_melanome_opt] = qualite_classification(Y_app_pred,Y_app); % FONCTION A CODER
% Classification des donnees de test
Y_test_pred = classification_foret(foret,X_test); % FONCTION A CODER
[pourcentage_bonne_classification_test_opt, pourcentage_bonne_classification_test_fibrome_opt, ...
 pourcentage_bonne_classification_test_melanome_opt] = qualite_classification(Y_test_pred,Y_test); % FONCTION A CODER

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

% Grille de classification avec l'arbre entre les 2 classes :
[grille_carac1,grille_carac2] = meshgrid(graduation_carac_1,graduation_carac_2);
X_grille = [grille_carac1(:),grille_carac2(:)];
Y_pred_grille = classification_foret(foret,X_grille); % FONCTION A CODER
Y_pred_grille = reshape(Y_pred_grille,length(graduation_carac_2),length(graduation_carac_1));

%--------------------------------------------------------------------------
% Affichage des donnees d'apprentissage 
%--------------------------------------------------------------------------

% Affichage des classes predites par le SVM pour l'apprentissage :
figure('Name','Classification par SVM avec marge souple (apprentissage)',...
       'Position',[0.02*L,0.1*H,0.47*L,0.7*H],...
       'Color',[0.7 0.75 0.85]);
    imagesc(graduation_carac_1,graduation_carac_2,Y_pred_grille)
    axis xy
    carte_couleurs = [1 0.5 0.5; 0.5 0.5 1];
    colormap(carte_couleurs)
    axis(limites_affichage)
    hold on

% Affichage des points de l'ensemble d'apprentissage :
    [f_ok,m_ok] = affichage_points_classes(X_app,Y_app,Y_app_pred);

    title(['Bonnes classifications (donnees d''aprentissage) : ' ...
           num2str(pourcentage_bonne_classification_app_opt,'%.1f') '%']);
    legend([f_ok,m_ok],...
           ['Fibromes bien classes (' num2str(pourcentage_bonne_classification_app_fibrome_opt,'%.1f') '%)'],...
           ['Melanomes bien classes (' num2str(pourcentage_bonne_classification_app_melanome_opt,'%.1f') '%)'],...
            'Location','NorthWest');
    set(gca,'FontSize',20);

%--------------------------------------------------------------------------
% Affichage des donnees de test 
%--------------------------------------------------------------------------

% Affichage des classes predites par le SVM pour le test :
figure('Name','Classification par SVM avec marge souple (test)',...
       'Position',[0.51*L,0.1*H,0.47*L,0.7*H],...
       'Color',[0.7 0.75 0.85]);
    imagesc(graduation_carac_1,graduation_carac_2,Y_pred_grille);
    axis xy
    carte_couleurs = [1 0.5 0.5; 0.5 0.5 1];
    colormap(carte_couleurs);
    axis(limites_affichage);
    hold on;

% Affichage des points de l'ensemble d'apprentissage :
    [f_ok,m_ok] = affichage_points_classes(X_test,Y_test,Y_test_pred);

    title(['Bonnes classifications (donnees de test) : ' ...
           num2str(pourcentage_bonne_classification_test_opt,'%.1f') '%']);
    legend([f_ok,m_ok],...
           ['Fibromes bien classes (' num2str(pourcentage_bonne_classification_test_fibrome_opt,'%.1f') '%)'],...
           ['Melanomes bien classes (' num2str(pourcentage_bonne_classification_test_melanome_opt,'%.1f') '%)'],...
           'Location','NorthWest');
    set(gca,'FontSize',20);

