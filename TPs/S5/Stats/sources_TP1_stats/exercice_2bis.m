exercice_2;

% Estimation de la droite de regression par resolution avec les covariances :
[a_Dyx_MC2,b_Dyx_MC2,coeff_r2] = ...
    estim_param_Dyx_MC2(x_donnees_bruitees,y_donnees_bruitees); % FONCTION A CODER

% Calcul et affichage de l'ecart angulaire :
theta_Dyx_MC2 = atan(-1/a_Dyx_MC2);
EA_Dyx_MC2 = abs(theta_Dyx_MC2-theta_0);
EA_Dyx_MC2 = min([EA_Dyx_MC2 180-EA_Dyx_MC2])/pi*180;

% Affichage de la droite de regression estimee par resolution avec les covariances :
f = figure('Name','Estimation par les moindres carres (v2)', ...
	       'Position',[0.51*L,0.1*H,0.48*L,0.7*H]);    
    x_Dyx_MC2 = [-taille;x_donnees_bruitees;taille];
    y_Dyx_MC2 = a_Dyx_MC2*x_Dyx_MC2+b_Dyx_MC2;
    hold on;
    for k = 2:length(x_Dyx_MC2)-1
        he = plot([x_Dyx_MC2(k) x_donnees_bruitees(k-1)],[y_Dyx_MC2(k) y_donnees_bruitees(k-1)], ...
                  'Color',[1 0.6 0.6]);
    end
    hd = plot(x_droite,y_droite,'b-','LineWidth',3);
    hmc = plot(x_Dyx_MC2,y_Dyx_MC2,'r','LineWidth',2);
    hdb = plot(x_donnees_bruitees,y_donnees_bruitees,'k*','MarkerSize',5,'LineWidth',2);
    axis equal;
    axis(bornes);
    grid on;

    title({['Ecart angulaire MC_{YX}^{v2} = ' num2str(EA_Dyx_MC2,'%.2f') '°'] ...
           ['Correlation au carre r^2 = ' num2str(coeff_r2,'%.2f')]})
    lg = legend([hd, hdb, hmc, he], ...
                '~Droite', ...
                '~Donnees bruitees', ...
                '~$D_{YX}$ (moindres carres)', ...
                '~Erreurs residuelles', ...
                'Location','SouthWest');
    set(lg,'Interpreter','Latex');
    hx = xlabel('$x$');
    set(hx,'Interpreter','Latex');
    hy = ylabel('$y$');
    set(hy,'Interpreter','Latex');
    set(gca,'FontSize',15);




