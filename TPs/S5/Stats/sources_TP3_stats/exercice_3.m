clear;
close all;
clc

taille_ecran = get(0,'ScreenSize');
L = taille_ecran(3);
H = taille_ecran(4);

% Fenetre d'affichage :
figure('Name','Points situes au voisinage d''un cercle', ...
	   'Position',[0.2*L,0.1*H,0.6*L,0.7*H]);
axis equal;
hold on;
set(gca,'FontSize',20);
hx = xlabel('$x$','FontSize',30);
set(hx,'Interpreter','Latex');
hy = ylabel('$y$','FontSize',30);
set(hy,'Interpreter','Latex');

% Bornes d'affichage des donnees centrees en (0,0) :
taille = 20;
bornes = [-taille taille -taille taille];

% Creation du cercle et des donnees bruitees :
n = 50;
sigma = 0.5;
[x_cercle,y_cercle,theta_cercle,x_donnees_bruitees,y_donnees_bruitees,theta_donnees_bruitees] ...
		= creation_cercle_et_donnees_bruitees(taille,n,sigma);

% Affichage du cercle :
plot(x_cercle([1:end 1]),y_cercle([1:end 1]),'r','LineWidth',3);

% Donnees aberrantes :
proportion = 0.25;
n_donnees_aberrantes = floor(proportion*n);
x_donnees_bruitees = [x_donnees_bruitees; taille*(2*rand(n_donnees_aberrantes,1)-1)];
y_donnees_bruitees = [y_donnees_bruitees; taille*(2*rand(n_donnees_aberrantes,1)-1)];

% Affichage des donnees bruitees :
plot(x_donnees_bruitees,y_donnees_bruitees,'k*','MarkerSize',5,'LineWidth',2);
axis(bornes);
lg = legend(' Cercle', ...
		' Donnees (bruitees + aberrantes)', ...
		'Location','Best');
grid on;
