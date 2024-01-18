clear;
close all;
clc

taille_ecran = get(0,'ScreenSize');
L = taille_ecran(3);
H = taille_ecran(4);

% Fenetre d'affichage :
figure('Name','Estimations de deux droites','Position',[0.3*L,0.1*H,0.4*L,0.7*H]);

% Bornes d'affichage des donnees centrees en (0,0) :
taille = 20;
bornes = [-taille taille -taille taille];

% Creation des 2 droites et des donnees bruitees : 
n = 100;
sigma = 1;
[x_droite,y_droite_1,theta_1,y_droite_2,theta_2,x_donnees_bruitees,y_donnees_bruitees] = ...
    creation_2droites_et_donnees_bruitees(taille,n,sigma);

% Affichage des 2 droites et des donnees bruitees :
    hold on;
    plot(x_droite,y_droite_1,'Color',[1,0,0],'LineWidth',3);
    plot(x_droite,y_droite_2,'Color',[0.6 0 0],'LineWidth',3,'HandleVisibility','off');
    plot(x_donnees_bruitees,y_donnees_bruitees,'k*','MarkerSize',7,'LineWidth',2);
    axis(bornes);
    legend(' Droites_{VT} ', ...
           ' Donnees', ...
           'Location','Best');
    axis equal;
    xlim([-taille taille]);
    ylim([-taille taille]);
    set(gca,'FontSize',15);
    hx = xlabel('$x$','FontSize',30);
    set(hx,'Interpreter','Latex');
    hy = ylabel('$y$','FontSize',30);
    set(hy,'Interpreter','Latex');
    grid on;
