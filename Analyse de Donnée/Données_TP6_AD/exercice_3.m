clear
close all
clc

% Parametres pour l'affichage des donnees :
taille_ecran = get(0,'ScreenSize');
L = taille_ecran(3);
H = taille_ecran(4);

% Chargement des donnees :
load donnees_classif_foret;

%%% A COMPLETER
% Entrainement de la foret aleatoire :
nb_arbres = 500;
fraction_data = .80;

foret = entrainement_foret(X_app,Y_app,nb_arbres,fraction_data);

% Classification des donnees d'apprentissage par la foret
Y_app_pred = classification_foret(foret, X_app);
MC_app = confusionmat(Y_app,Y_app_pred);

% Classification des donnees de test par la foret
Y_test_pred = classification_foret(foret, X_test);
[MC_test,classes] = confusionmat(Y_test,Y_test_pred);

%--------------------------------------------------------------------------
% Affichage de la matrice de confusion pour l'ensemble d'apprentissage
%--------------------------------------------------------------------------

figure('Name','Classification de forets par foret aleatoire (apprentissage)',...
       'Position',[0.02*L,0.1*H,0.47*L,0.7*H],...
       'Color',[0.7 0.75 0.85]);
    confusionchart(MC_app,classes,'RowSummary','row-normalized');
    title('Matrice de confusion (donnees d''aprentissage)');
    xlabel('Y_{pred}');
    ylabel('Y');
    set(gca,'FontSize',15);

%--------------------------------------------------------------------------
% Affichage de la matrice de confusion pour l'ensemble d'apprentissage
%--------------------------------------------------------------------------

figure('Name','Classification de forets par foret aleatoire (test)',...
       'Position',[0.51*L,0.1*H,0.47*L,0.7*H],...
       'Color',[0.7 0.75 0.85]);
    confusionchart(MC_test,classes,'RowSummary','row-normalized');
    title('Matrice de confusion (donnees de test)');
    xlabel('Y_{pred}');
    ylabel('Y');
    set(gca,'FontSize',15);
