clear
close all
clc

% Parametres pour l'affichage des donnees :
taille_ecran = get(0,'ScreenSize');
L = taille_ecran(3);
H = taille_ecran(4);

%--------------------------------------------------------------------------
% Classification avec un arbre de classification
%--------------------------------------------------------------------------

% Donnees non filtrees :
load donnees_carac;
X_app = X_app(:,1:2);
X_test = X_test(:,1:2);
Y_app(Y_app == 2) = -1; % Changement du label pour utiliser le SVM
Y_test(Y_test == 2) = -1; % Changement du label pour utiliser le SVM
nb_donnees_app = size(X_app,1);
nb_donnees_test = size(X_test,1);

% Calcul et affichage de la premiere decoupe
[valeur_coupure,ind_variable_coupure] = premiere_coupure(X_app,Y_app);

disp(['La premiere decoupe se fait sur la variable x' num2str(ind_variable_coupure) ...
      ' a la valeur ' num2str(valeur_coupure) '.'])