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

% Modelisation de la silhouette par deux courbes de Bezier couplees :
figure('Name','Modelisation de la silhouette par deux courbes de Bezier couplees',...
	   'Position',[0.2*L,0.1*H,0.6*L,0.7*H],...
       'Color',[0.7 0.75 0.85]);
   
[p,n] = size(bord_inf);
x = transpose(0:1/(p-1):1);
liste_parametres_MC = zeros(2*d-1,n);
for j = 1:n
    
    % Calcul des moindres carres et creation des deux modeles pour les bords :
	parametres_MC = estim_param_MC_paire(d,x,bord_inf(:,j),bord_sup(:,j));	    % FONCTION A CODER
	y_inf = courbe_bezier(x,[beta_0;parametres_MC(1:d-1);parametres_MC(end)]);
	y_sup = courbe_bezier(x,[gamma_0;parametres_MC(d:end)]);

    % Affichage des donnees et des courbes :
	hd = plot(x,bord_inf(:,j),'k*-','LineWidth',2);
	hold on;
	hi = plot(x,y_inf,'r','LineWidth',3);
	plot(x,bord_sup(:,j),'k*-','LineWidth',2);
	hs = plot(x,y_sup,'b','LineWidth',3);
	axis([0,1.01,60,150]);
	axis ij;
    grid on;
    
    title('Modelisation de la paire de silouhettes');
    legend([hd, hi, hs],...
           'Donnees','Modele du bord inferieur','Modele du bord superieur');
	set(gca,'FontSize',20);
	xlabel('$x$','FontSize',30,'Interpreter','Latex');
	ylabel('$y$','FontSize',30,'Interpreter','Latex','Rotation',0);

	pause(0.5);
	hold off;
	liste_parametres_MC(:,j) = parametres_MC;
end

save liste_parametres_MC liste_parametres_MC;
