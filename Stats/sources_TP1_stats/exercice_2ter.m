exercice_2;

% Estimation de la droite de regression par resolution de systeme lineaire en Matlab :
mdl = fitlm(x_donnees_bruitees,y_donnees_bruitees);
% Recuperation des parametres du modele
a_Dyx_MC3 = mdl.Coefficients.Estimate(2);
b_Dyx_MC3 = mdl.Coefficients.Estimate(1);
coeff_R2o = mdl.Rsquared.Ordinary;
disp(mdl)

% Calcul et affichage de l'ecart angulaire :
theta_Dyx_MC3 = atan(-1/a_Dyx_MC3);
EA_Dyx_MC3 = abs(theta_Dyx_MC3-theta_0);
EA_Dyx_MC3 = min([EA_Dyx_MC3 pi-EA_Dyx_MC3])/pi*180;

% Affichage de la droite de regression estimee par resolution de systeme lineaire en Matlab :
figure('Name','Estimation par les moindres carres (v3)', ...
	   'Position',[0.51*L,0.1*H,0.48*L,0.7*H]);
    hd = plot(x_droite,y_droite,'b-','LineWidth',3);
    hold on;
    hmc = plot(mdl);
    hmc(1).Visible = 'off';
    hmc(2).LineWidth = 3;
    hmc(2).Color = 'r';
    hmc(3).LineWidth = 2;
    hmc(3).Color = 'r';
    hdb = plot(x_donnees_bruitees,y_donnees_bruitees,'k*','MarkerSize',5,'LineWidth',2);
    axis equal;
    axis(bornes);
    grid on;

    t = title({['Ecart angulaire MC_{YX}^{v3} = ' num2str(EA_Dyx_MC3,'%.2f') '°'] ...
               ['Coefficient de determination R^2 = ' num2str(coeff_R2o,'%.2f')]});
    set(t,'Interpreter','tex');
    lg = legend([hd, hdb, hmc(2), hmc(3)], ...
                '~Droite', ...
                '~Donnees bruitees', ...
                '~$D_{YX}$ (moindres carres)', ...
                '~Intervalle de confiance a 95\%', ...
                'Location','SouthWest');
    set(lg,'Interpreter','Latex');
    hx = xlabel('$x$');
    set(hx,'Interpreter','Latex');
    hy = ylabel('$y$');
    set(hy,'Interpreter','Latex');
    set(gca,'FontSize',15);



