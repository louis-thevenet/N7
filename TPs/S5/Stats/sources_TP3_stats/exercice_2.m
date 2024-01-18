clear;
close all;
clc;

taille_ecran = get(0,'ScreenSize');
L = taille_ecran(3);
H = taille_ecran(4);

load exercice_0;

% Parametres de l'algorithme RANSAC :
n = length(rho);
S_ecart = 5;
S_prop = 0.3;
k_max = floor(nchoosek(n,2)/n);
parametres = [S_ecart S_prop k_max];

%--------------------------------------------------------------------------------------

% Estimation du premier point de fuite :
[rho_F_1,theta_F_1] = RANSAC_2droites(rho,theta,parametres);
x_F_1 = rho_F_1*cos(theta_F_1);
y_F_1 = rho_F_1*sin(theta_F_1);

% Droites conformes au premier point de fuite :
conformes_1 = abs(rho-rho_F_1*cos(theta-theta_F_1))<=S_ecart;
rho_conformes_1 = rho(conformes_1);
theta_conformes_1 = theta(conformes_1);

% Droites restantes :
theta_restants = theta(~conformes_1);
rho_restants = rho(~conformes_1);

% Limites des affichages :
marge = round(min(nb_lignes,nb_colonnes)/10);
x_min = min([1 x_F_1])-marge;
x_max = max([nb_colonnes x_F_1])+marge;
y_min = min([1 y_F_1])-marge;
y_max = max([nb_lignes y_F_1])+marge;
limites_affichages = [x_min x_max y_min y_max];

% Selection des droites formant le premier faisceau :
taille_selection_1 = min(length(rho_conformes_1),10);
longueurs_segments_au_carre_1 = (extremites(1,1,conformes_1)-extremites(1,2,conformes_1)).^2 ...
				+(extremites(2,1,conformes_1)-extremites(2,2,conformes_1)).^2;
[~,indices_tries_1] = sort(longueurs_segments_au_carre_1,'descend');
selection_1 = indices_tries_1(1:taille_selection_1);

% Affichage de la 1ere sinusoide et des points de coordonnees (rho,theta) :
figure('Name','Estimation de la ligne de fuite','Position',[0.1*L,0.1*H,0.8*L,0.7*H]);
subplot(1,2,1);

    % Affichage de la sinusoide correspondant au premier point de fuite :
    theta_affichage = (-pi:0.01:pi)';
    rho_affichage_1 = rho_F_1*cos(theta_affichage-theta_F_1);
    hs1 = plot(theta_affichage,rho_affichage_1,'Color',[1 0.5 0.5],'LineWidth',3);
    hold on;
    
    % Affichage des points conformes a la premiere sinusoide VS restants :
    hr = plot(theta_restants,rho_restants,'k*','MarkerSize',5,'LineWidth',2);
    hd1 = plot(theta_conformes_1,rho_conformes_1,'r*','MarkerSize',5,'LineWidth',2);
    axis([-pi pi 1.1*max(abs([rho;rho_F_1]))*[-1 1]]);
    grid on;
    
    title('Estimation du point de fuite n°1');
    hx = xlabel('$\theta$');
    set(hx,'Interpreter','Latex');
    hy = ylabel('$\rho$');
    set(hy,'Interpreter','Latex');
    set(gca,'FontSize',20);
    legend([hs1, hd1, hr], ...
           'Sinusoide estimee pour le point de fuite n°1', ...
           'Droites en direction du point de fuite n°1', ...
           'Droites restantes', ...
           'Location', 'southoutside')

% Affichage de l'image avec les droites et le point de fuite :
subplot(1,2,2)
    imagesc(I);
    colormap gray;
    axis image off;
    hold on;
    hf1 = affichage_faisceau(rho_conformes_1(selection_1),theta_conformes_1(selection_1), ...
                             limites_affichages,'r');
    hpf1 = plot(x_F_1,y_F_1,'Color',[1 0.5 0.5], ...
                            'Marker','*','MarkerSize',10, ...
                            'LineStyle','none','LineWidth',5);
    axis(limites_affichages);
    
    title('Localisation du point de fuite n°1');
    set(gca,'FontSize',20);
    legend([hf1, hpf1], ...
           'Droites en direction du point de fuite n°1', ...
           'Point de fuite estime n°1', ...
           'Location','southoutside')
