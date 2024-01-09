clear;
close all;
clc;

taille_ecran = get(0,'ScreenSize');
L = taille_ecran(3);
H = taille_ecran(4);

load exercice_0;

% Estimation du point de fuite :
[rho_F,theta_F] = estim_param_F(rho,theta);
x_F = rho_F*cos(theta_F);
y_F = rho_F*sin(theta_F);

% Limites des affichages sur l'image :
marge = round(min(nb_lignes,nb_colonnes)/10);
x_min = min([1,x_F])-marge;
x_max = max([nb_colonnes,x_F])+marge;
y_min = min([1,y_F])-marge;
y_max = max([nb_lignes,y_F])+marge;
limites_affichages = [x_min x_max y_min y_max];

% Selection des droites formant le faisceau :
taille_selection = min(length(rho),10);
longueurs_segments_au_carre = (extremites(1,1,:)-extremites(1,2,:)).^2 ...
                +(extremites(2,1,:)-extremites(2,2,:)).^2;
[~,indices_tries] = sort(longueurs_segments_au_carre,'descend');
selection = indices_tries(1:taille_selection);

% Affichage de la sinusoide et des points de coordonnees (rho,theta) :
figure('Name','Estimation et localisation du point de fuite','Position',[0.1*L,0.1*H,0.8*L,0.7*H]);
subplot(1,2,1);
    pas = 0.01;
    theta_affichage = (-pi:pas:pi)';
    rho_affichage = rho_F*cos(theta_affichage-theta_F);
    hs = plot(theta_affichage,rho_affichage,'Color',[1 0.5 0.5],'LineWidth',3);
    hold on;
    hd = plot(theta,rho,'r*','MarkerSize',5,'LineWidth',2);
    axis([-pi pi 1.1*max(abs([rho;rho_F]))*[-1 1]]);
    grid on;

    title('Estimation du point de fuite');
    hx = xlabel('$\theta$');
    set(hx,'Interpreter','Latex');
    hy = ylabel('$\rho$');
    set(hy,'Interpreter','Latex');
    set(gca,'FontSize',20);
    legend([hs, hd], ...
           'Sinusoide estimee pour le point de fuite', ...
           'Droites en direction du point de fuite')

% Affichage de l'image avec les droites et le point de fuite :
subplot(1,2,2);
    imagesc(I);
    axis image off;
    colormap gray;
    hold on;
    hf = affichage_faisceau(rho(selection),theta(selection), ...
                            limites_affichages,'r');
    hpf = plot(x_F,y_F,'Color',[1 0.5 0.5], ...
                       'Marker','*','MarkerSize',10, ...
                       'LineStyle','none','LineWidth',5);
    axis(limites_affichages);
           
    title('Localisation du point de fuite');
    set(gca,'FontSize',20);
    legend([hf, hpf], ...
           'Droites en direction du point de fuite', ...
           'Point de fuite estime', ...
           'Location','southoutside')
