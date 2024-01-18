exercice_2;
title(['Ecart angulaire MC_{YX} = ' num2str(EA_Dyx_MC1,'%.2f') '°'])

%-----------------------------------------------------------------------------------
% Dorth par moindres carres
%-----------------------------------------------------------------------------------
                 
% Estimation de la droite de regression par resolution du systeme CY = 0 :
[theta_Dorth_MC,rho_Dorth_MC] = ...
    estim_param_Dorth_MC(x_donnees_bruitees,y_donnees_bruitees); % FONCTION A CODER

% Calcul de l'ecart angulaire :
EA_Dorth_MC = abs(theta_Dorth_MC-theta_0);
EA_Dorth_MC = min([EA_Dorth_MC pi-EA_Dorth_MC])/pi*180;

% Affichage de la droite de regression estimee par le maximum de vraisemblance :
figure('Name','Estimation par les moindres carres', ...
	   'Position',[0.51*L,0.1*H,0.48*L,0.7*H]);
    x_Dorth_MC = [-taille;x_donnees_bruitees;taille];
    y_Dorth_MC = (rho_Dorth_MC-x_Dorth_MC*cos(theta_Dorth_MC))/sin(theta_Dorth_MC);
    xp_Dorth_MC = (x_donnees_bruitees + cos(theta_Dorth_MC)/sin(theta_Dorth_MC)* ...
                  (rho_Dorth_MC/sin(theta_Dorth_MC) - y_donnees_bruitees))/ ...
                  (1 + (cos(theta_Dorth_MC)/sin(theta_Dorth_MC))^2);
    yp_Dorth_MC = rho_Dorth_MC/sin(theta_Dorth_MC) - cos(theta_Dorth_MC)/sin(theta_Dorth_MC)*xp_Dorth_MC;
    hd = plot(x_droite,y_droite,'b-','LineWidth',3);
    hold on;
    hmc = plot(x_Dorth_MC,y_Dorth_MC,'r','LineWidth',3);
    for k = 2:length(x_Dorth_MC)-1
        he = plot([xp_Dorth_MC(k-1) x_donnees_bruitees(k-1)],[yp_Dorth_MC(k-1) y_donnees_bruitees(k-1)], ...
                  'Color',[1 0.6 0.6]);
    end
    hdb = plot(x_donnees_bruitees,y_donnees_bruitees,'k*','MarkerSize',5,'LineWidth',2);
    axis equal;
    axis(bornes);
    grid on;

    title(['Ecart angulaire MC_{orth} = ' num2str(EA_Dorth_MC,'%.2f') '°'])
    hold on;
    hx = xlabel('$x$');
    set(hx,'Interpreter','Latex');
    hy = ylabel('$y$');
    set(hy,'Interpreter','Latex');
    set(gca,'FontSize',15);
    lg = legend([hd, hdb, hmc, he], ...
                '~Droite', ...
                '~Donnees bruitees', ...
                '~$D_\perp$ (moindres carres)', ...
                '~Erreurs residuelles', ...
                'Location','SouthWest');
    set(lg,'Interpreter','Latex');
    
    
    