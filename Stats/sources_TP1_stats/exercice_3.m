exercice_1;

%-----------------------------------------------------------------------------------
% Dorth par maximum de vraisemblance
%-----------------------------------------------------------------------------------

% Estimation de la droite de regression par le maximum de vraisemblance :
n_tirages = 100;
tirages_theta = tirages_aleatoires_uniformes(n_tirages);
[theta_Dorth_MV,rho_Dorth_MV] = ...
    estim_param_Dorth_MV(x_donnees_bruitees,y_donnees_bruitees,tirages_theta); % FONCTION A CODER

% Calcul de l'ecart angulaire :
EA_Dorth_MV = abs(theta_Dorth_MV-theta_0);
EA_Dorth_MV = min([EA_Dorth_MV pi-EA_Dorth_MV])/pi*180;

% Affichage de la droite de regression estimee par le maximum de vraisemblance Orth :
figure('Name','Estimation par le maximum de vraisemblance', ...
	   'Position',[0.51*L,0.1*H,0.48*L,0.7*H]);  
    x_Dorth_MV = [-taille;x_donnees_bruitees;taille];
    y_Dorth_MV = (rho_Dorth_MV-x_Dorth_MV*cos(theta_Dorth_MV))/sin(theta_Dorth_MV);
    xp_Dorth_MV = (x_donnees_bruitees + cos(theta_Dorth_MV)/sin(theta_Dorth_MV)* ...
                  (rho_Dorth_MV/sin(theta_Dorth_MV) - y_donnees_bruitees))/ ...
                  (1 + (cos(theta_Dorth_MV)/sin(theta_Dorth_MV))^2);
    yp_Dorth_MV = rho_Dorth_MV/sin(theta_Dorth_MV) - cos(theta_Dorth_MV)/sin(theta_Dorth_MV)*xp_Dorth_MV;
    hd = plot(x_droite,y_droite,'b-','LineWidth',3);
    hold on;
    hmv = plot(x_Dorth_MV,y_Dorth_MV,'r','LineWidth',3);
    for k = 2:length(x_Dorth_MV)-1
        he = plot([xp_Dorth_MV(k-1) x_donnees_bruitees(k-1)],[yp_Dorth_MV(k-1) y_donnees_bruitees(k-1)], ...
                  'Color',[1 0.6 0.6]);
    end
    hdb = plot(x_donnees_bruitees,y_donnees_bruitees,'k*','MarkerSize',5,'LineWidth',2);
    axis equal;
    axis(bornes);
    grid on;

    title(['Ecart angulaire MV_{orth} = ' num2str(EA_Dorth_MV,'%.2f') '°'])
    hold on;
    hx = xlabel('$x$');
    set(hx,'Interpreter','Latex');
    hy = ylabel('$y$');
    set(hy,'Interpreter','Latex');
    set(gca,'FontSize',15);
    lg = legend([hd, hdb, hmv, he], ...
                '~Droite', ...
                '~Donnees bruitees', ...
                '~$D_\perp$ (maximum de vraisemblance)', ...
                '~Erreurs residuelles', ...
                'Location','SouthWest');
    set(lg,'Interpreter','Latex');

