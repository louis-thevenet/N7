clear;
close all;
clc;

% Parametres d'affichage :
taille_ecran = get(0,'ScreenSize');
L = taille_ecran(3);
H = taille_ecran(4);

%--------------------------------------------------------------------------
% Affichage des donnees d'apprentissage non filtrees
%--------------------------------------------------------------------------

% Donnees non filtrees :
load donnees_carac;

% Parametres d'affichage :
marge = 0.005;
limites_affichage = [min(min(X_app(:,1)))-marge max(max(X_app(:,1)))+marge...
			         min(min(X_app(:,2)))-marge max(max(X_app(:,2)))+marge];
nom_carac_1 = 'Compacite';
nom_carac_2 = 'Contraste';

% Affichage des donnees :
figure('Name','Representation des images par des points 2D',...
       'Position',[0.02*L,0.1*H,0.47*L,0.7*H],...
       'Color',[0.7 0.75 0.85]);
    hold on;
    [f_ok,m_ok] = affichage_points_classes(X_app,Y_app,Y_app);
    grid on;
    axis(limites_affichage);
    
    title('Donnees d''apprentissage non separables')
    xlabel(nom_carac_1);
    ylabel(nom_carac_2);
    legend([f_ok,m_ok],'Fibromes','Melanomes','Location','NorthWest');
    set(gca,'FontSize',20);

%--------------------------------------------------------------------------
% Affichage des donnees d'apprentissage filtrees
%--------------------------------------------------------------------------

% Donnees filtrees :
load donnees_carac_filtrees;

% Parametres d'affichage :
marge = 0.005;
limites_affichage = [min(min(X_app(:,1)))-marge max(max(X_app(:,1)))+marge...
			         min(min(X_app(:,2)))-marge max(max(X_app(:,2)))+marge];
nom_carac_1 = 'Compacite';
nom_carac_2 = 'Contraste';

% Affichage des donnees filtrees :
figure('Name','Representation des images par des points 2D',...
       'Position',[0.51*L,0.1*H,0.47*L,0.7*H],...
       'Color',[0.7 0.75 0.85]);
    hold on;
    [f_ok,m_ok] = affichage_points_classes(X_app,Y_app,Y_app);
    grid on;
    axis(limites_affichage);
    
    title('Donnees d''apprentissage separables')
    xlabel(nom_carac_1);
    ylabel(nom_carac_2);
    legend([f_ok,m_ok],'Fibromes','Melanomes','Location','NorthWest');
    set(gca,'FontSize',20);
