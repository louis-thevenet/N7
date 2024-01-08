exercice_3;

n_tests = 1000;

% Parametres de l'algorithme RANSAC :
n = length(x_donnees_bruitees);
S_ecart = 3;
S_prop = 0.5;
k_max = floor(nchoosek(n,3)/n);
parametres = [S_ecart S_prop k_max n_tests];

% Estimation du rayon et de la position du centre :
[C_estime,R_estime] = RANSAC_3points(x_donnees_bruitees,y_donnees_bruitees,parametres);

% Affichage du cercle estime :
x_cercle_estime = C_estime(1) + R_estime*cos(theta_cercle);
y_cercle_estime = C_estime(2) + R_estime*sin(theta_cercle);
plot(x_cercle_estime([1:end 1]),y_cercle_estime([1:end 1]),'b','LineWidth',3);

% Affichage des points conformes au modele :
conformes = (abs(sqrt((x_donnees_bruitees-C_estime(1)).^2 + ...
			 (y_donnees_bruitees-C_estime(2)).^2)-R_estime)<=S_ecart);
plot(x_donnees_bruitees(conformes),y_donnees_bruitees(conformes),'b*','MarkerSize',5,'LineWidth',2);
lg = legend(' Cercle initial', ...
		    ' Donnees (bruitees + aberrantes)', ...
		    ' Cercle estime', ...
		    ' Donnees conformes', ...
		    'Location','Best');
