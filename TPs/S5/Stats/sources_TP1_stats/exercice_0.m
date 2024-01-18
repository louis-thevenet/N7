clear;
close all;
clc

taille_ecran = get(0,'ScreenSize');
L = taille_ecran(3);
H = taille_ecran(4);

% Fenetre d'affichage :
figure('Name','Points situes au voisinage d''une droite', ...
	   'Position',[0.3*L,0.1*H,0.4*L,0.7*H]);
axis equal;
hold on;
hx = xlabel('$x$');
set(hx,'Interpreter','Latex');
hy = ylabel('$y$');
set(hy,'Interpreter','Latex');
set(gca,'FontSize',15);

% Creation de la droite et des donnees bruitees :
taille = 20;
bornes = [-taille taille -taille taille];
n = 100;
sigma = 2;
[x_droite,y_droite,x_donnees_bruitees,y_donnees_bruitees, theta_0, rho_0] ...
			         = creation_droite_et_donnees_bruitees(taille,n,sigma);

% Affichage de la droite :
hd = plot(x_droite,y_droite,'b-','LineWidth',3);

% Affichage des donnees bruitees :
hdb = plot(x_donnees_bruitees,y_donnees_bruitees,'k*','MarkerSize',5,'LineWidth',2);
axis(bornes);
grid on;
lg = legend([hd, hdb], ...
            '~Droite', ...
	        '~Donnees bruitees', ...
	        'Location','Best');
set(lg,'Interpreter','Latex');
