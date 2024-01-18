donnees;

% Estimation de la position du centre :
[G, R_moyen] = calcul_G_et_R_moyen(x_donnees_bruitees,y_donnees_bruitees); % FONCTION A CODER

% Affichage du cercle estime :
theta_cercle = 2*pi/100:2*pi/100:2*pi;
x_cercle_estime = G(1) + R_moyen*cos(theta_cercle);
y_cercle_estime = G(2) + R_moyen*sin(theta_cercle);
plot(x_cercle_estime([1:end 1]),y_cercle_estime([1:end 1]),'b','LineWidth',3);
legend(' Cercle initial', ...
	   ' Donnees bruitees', ...
	   ' Estimation avec G et R_{moyen}', ...
	   'Location','Best');
   
clear theta_cercle x_cercle_estime y_cercle_estime