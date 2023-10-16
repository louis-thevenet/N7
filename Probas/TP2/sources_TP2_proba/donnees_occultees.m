clear;
close all;
clc;

taille_ecran = get(0,'ScreenSize');
L = taille_ecran(3);
H = taille_ecran(4);

% Fenetre d'affichage :
figure('Name','Points situes au voisinage d''un cercle', ...
	   'Position',[0.2*L,0.05*H,0.6*L,0.7*H]);
axis equal;
hold on;
set(gca,'FontSize',20);
hx = xlabel('$x$','FontSize',30);
set(hx,'Interpreter','Latex');
hy = ylabel('$y$','FontSize',30);
set(hy,'Interpreter','Latex');

% Creation du cercle reel et des donnees bruitees :
n = 70;
sigma = 0.5;
[bornes,x_cercle,y_cercle,...
 x_donnees_bruitees,y_donnees_bruitees,theta_donnees_bruitees] ...
		                    = creation_cercle_et_donnees_bruitees(n,sigma);

% Affichage du cercle :
plot(x_cercle([1:end 1]),y_cercle([1:end 1]),'r','LineWidth',3);

% Occultation de certains points :
thetas = 2*pi*rand(1,2);
[x_donnees_bruitees,y_donnees_bruitees] = ...
occultation_donnees(x_donnees_bruitees,y_donnees_bruitees, ...
                    theta_donnees_bruitees, thetas); % FONCTION A CODER

% Affichage des donnees bruitees occultees :
plot(x_donnees_bruitees,y_donnees_bruitees,'k*','MarkerSize',5,'LineWidth',2);
axis(bornes);
legend(' Cercle', ...
	   ' Donnees bruitees occultees', ...
	   'Location','Best');
grid on;

clear taille_ecran L H hx hy n sigma bornes x_cercle y_cercle
