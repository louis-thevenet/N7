clear;
close all;
clc;

taille_ecran = get(0,'ScreenSize');
L = taille_ecran(3);
H = taille_ecran(4);

% Chargement et initialisations :
load donnees;
load liste_parametres_MC;
beta_0 = bord_inf(1,1);
gamma_0 = bord_sup(1,1);

% Estimation des lois normales :
[moyennes,ecarts_types] = estim_moments(liste_parametres_MC); % FONCTION A CODER

% Simulation de silhouettes par tirages aleatoires :
figure('Name','Tirage aleatoire de silhouettes',...
	   'Position',[0.2*L,0.1*H,0.6*L,0.7*H],...
       'Color',[0.7 0.75 0.85]);
   
p = size(bord_inf,1);
x = transpose(0:1/(p-1):1);
nb_images = 30; % Longueur de la sequence simulee
for j = 1:nb_images
    
    % Genreations aleatoires des silouhettes :
	[y_inf,y_sup] = generation_aleatoire_courbe(x,moyennes,ecarts_types,beta_0,gamma_0); % FONCTION A CODER

    % Affichage des courbes :
	if sum(y_inf<y_sup)==0
		hi = plot(x,y_inf,'Color','r','LineWidth',2);
		hold on;
		hs = plot(x,y_sup,'Color','b','LineWidth',2);
		axis([0,1.01,30,180]);
		axis ij;
        grid on;
        
        title('Generation de paires de silouhettes');
        legend([hi, hs],...
               'Modele du bord inferieur','Modele du bord superieur');
		set(gca,'FontSize',20);
		xlabel('$x$','FontSize',30,'Interpreter','Latex');
		ylabel('$y$','FontSize',30,'Interpreter','Latex','Rotation',0);

		pause(0.5);
		hold off;
	end
end

save parametres_moments moyennes ecarts_types;
