clear;
close all;
clc;

taille_ecran = get(0,'ScreenSize');
L = taille_ecran(3);
H = taille_ecran(4);

% Chargement et initialisations :
load donnees;
beta_0 = bord_inf(1,1);
gamma_0 = bord_sup(1,1);

% Degre des courbes de Bezier (testez plusieurs valeurs) :
d = 5;

% Modelisation de la silhouette par deux courbes de Bezier independantes :
figure('Name','Modelisation par deux courbes de Bezier independantes',...
       'Position',[0.2*L,0.1*H,0.6*L,0.7*H],...
       'Color',[0.7 0.75 0.85]);
   
[p,n] = size(bord_inf);
x = transpose(0:1/(p-1):1);
for j = 1:n
    
    % Calcul des moindres carres et creation de la modele pour le bord inferieur :
	beta = estim_param_MC(d,x,bord_inf(:,j));		% FONCTION A CODER
	y_inf = courbe_bezier(x,[beta_0;beta]);	

    % Calcul des moindres carres et creation de la modele pour le bord superieur :
	gamma = estim_param_MC(d,x,bord_sup(:,j));		% FONCTION A CODER
	y_sup = courbe_bezier(x,[gamma_0;gamma]);
    
    % Affichage des donnees et des courbes :
	hd = plot(x,bord_inf(:,j),'k*-','LineWidth',2);
    hold on;
	hi = plot(x,y_inf,'r','LineWidth',3);
	plot(x,bord_sup(:,j),'k*-','LineWidth',2);
	hs = plot(x,y_sup,'b','LineWidth',3);
	axis([0,1.01,60,150]);
	axis ij;
    grid on;
    
    title('Modelisation des silouhettes separement');
    legend([hd, hi, hs],...
           'Donnees','Modele du bord inferieur','Modele du bord superieur');
	set(gca,'FontSize',20);
	xlabel('$x$','FontSize',30,'Interpreter','Latex');
	ylabel('$y$','FontSize',30,'Interpreter','Latex','Rotation',0);
	

	pause(0.5);
	hold off;
end
