clear
close all
clc

taille_ecran = get(0,'ScreenSize');
L = taille_ecran(3);
H = taille_ecran(4);

% Creation de la droite et des donnees bruitees :
taille = 20;
bornes = [-taille taille -taille taille];
n = 150;
sigma = 2;
[x_droite,y_droite,x_donnees_bruitees,y_donnees_bruitees, theta_0, rho_0] ...
			         = creation_droite_et_donnees_bruitees(taille,n,sigma);

% Estimation de la droite de regression par resolution du systeme AX = B :
[a_Dyx_MC1,b_Dyx_MC1,coeff_R2] = ...
    estim_param_Dyx_MC1(x_donnees_bruitees,y_donnees_bruitees); % FONCTION A CODER

% Calcul et affichage de l'ecart angulaire :
theta_Dyx_MC1 = atan(-1/a_Dyx_MC1);
EA_Dyx_MC1 = abs(theta_Dyx_MC1-theta_0);
EA_Dyx_MC1 = min([EA_Dyx_MC1 pi-EA_Dyx_MC1])/pi*180;

% Affichage de la droite de regression estimee par resolution du systeme AX = B :
f = figure('Name','Estimation par les moindres carres (v1)', ...
	       'Position',[0.01*L,0.1*H,0.48*L,0.7*H]);
    x_Dyx_MC1 = [-taille;x_donnees_bruitees;taille];
    y_Dyx_MC1 = a_Dyx_MC1*x_Dyx_MC1+b_Dyx_MC1;
    hold on;
    for k = 2:length(x_Dyx_MC1)-1
        he = plot([x_Dyx_MC1(k) x_donnees_bruitees(k-1)],[y_Dyx_MC1(k) y_donnees_bruitees(k-1)], ...
                  'Color',[1 0.6 0.6]);
    end
    hd = plot(x_droite,y_droite,'b-','LineWidth',3);
    hmc = plot(x_Dyx_MC1,y_Dyx_MC1,'r','LineWidth',3);
    hdb = plot(x_donnees_bruitees,y_donnees_bruitees,'k*','MarkerSize',5,'LineWidth',2);
    axis equal;
    axis(bornes);
    grid on;

    title({['Ecart angulaire MC_{YX}^{v1} = ' num2str(EA_Dyx_MC1,'%.2f') '°'] ...
           ['Coefficient de determination R^2 = ' num2str(coeff_R2,'%.2f')]})
    hx = xlabel('$x$');
    set(hx,'Interpreter','Latex');
    hy = ylabel('$y$');
    set(hy,'Interpreter','Latex');
    set(gca,'FontSize',15);
    lg = legend([hd, hdb, hmc, he], ...
                '~Droite', ...
                '~Donnees bruitees', ...
                '~$D_{YX}$ (moindres carres)', ...
                '~Erreurs residuelles', ...
                'Location','SouthWest');
    set(lg,'Interpreter','Latex');



