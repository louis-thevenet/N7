clear;
close all;
clc;

taille_ecran = get(0,'ScreenSize');
L = taille_ecran(3);
H = taille_ecran(4);

% Parametres :
set(0,'RecursionLimit',1000);		% Pour eviter les erreurs a l'execution
alpha = pi/8;						% Seuil sur l'orientation du gradient (en radians)
cos_alpha = cos(alpha);
seuil_norme = 2/sin(alpha);			% Seuil sur la norme du gradient (decoule d'une etude theorique)

% Lecture de l'image :
I = imread('Images/Piree.png');
% I = imread('Images/chaises.png');
% I = imread('Images/Morlaix.png');
if (ndims(I) == 3)
	I = rgb2gray(I);
end
I = imresize(I,0.8);			   % Permet de limiter l'effet de crenelage
[nb_lignes,nb_colonnes] = size(I);

% Parametres :
diagonale = floor(sqrt(nb_lignes^2+nb_colonnes^2));
card_max = floor(diagonale/2);				% Cardinal max d'un ensemble E
card_min = floor(card_max/20);				% Cardinal min d'un ensemble E

% Gradient du niveau de gris (x vers la droite, y vers le bas) :
I = double(I);
[G_x,G_y] = gradient(I);
G_norme = sqrt(G_x.^2+G_y.^2);

% Affichage de l'image :
figure('Name','Ensembles candidats','Position',[0.1*L,0.1*H,0.8*L,0.65*H]);    
subplot(1,3,1)
    imagesc(G_norme)
    axis image off
    colormap jet
    title('Norme des gradients','FontSize',30)

% Selection des pixels de contour :
contour = (G_norme > seuil_norme);

% Pas de pixel de contour sur le bord de l'image (traitement simplifie !) :
contour([1,nb_lignes],:) = 0;
contour(:,[1,nb_colonnes]) = 0;

% Affichage d'une petite fleche sur les pixels de contour :
[i,j] = find(contour);
subplot(1,3,2)
    imagesc(I)
    axis image off;
    colormap gray
    hold on
    quiver(j,i,G_x(contour),G_y(contour),'r')  % Attention : x = j et y = i
    title('Pixels de contour','FontSize',30)

    
% Boucle de traitement des pixels de contour :
% Positions relatives des 8 plus proches voisins
voisins = [ -1 -1 ; -1 0 ; -1  1 ; ...
             0 -1 ;         0  1 ; ...
		     1 -1 ;  1 0 ;  1  1 ];	
liste_E = [];

% Initialisation du 3eme affichage
subplot(1,3,3);
    imagesc(I*0);
    axis image off;
    title('Traitement en cours ...','FontSize',30);
    drawnow;

while any(contour(:))

	% Pixel de contour dont la norme du gradient est la plus elevee = "germe" :  
    G_norme_seuillee = G_norme.*contour;
    
    [~,j_germe] = max(max(G_norme_seuillee));
    [~,i_germe] = max(G_norme_seuillee(:,j_germe));
    
    % Remarque : 
    % les coordonnees des pixels seront a mettre les uns en dessous des autres
	E = [i_germe,j_germe];
    
    % Initialisation de la somme des gradients de E avec le germe :
	G_somme = [G_x(i_germe,j_germe),G_y(i_germe,j_germe)];
    
	% Construction recursive de l'ensemble E :
	[E,contour] = ensemble_E_recursif(E,contour,G_somme,i_germe,j_germe,...
                                      voisins,G_x,G_y,card_max,cos_alpha);

	% Ajout de l'ensemble E a la liste d'ensembles E, si son cardinal est superieur a card_min :
	if (size(E,1) >= card_min)
		liste_E = [liste_E;{E}];  % Concatenation d'une cellule {E} a liste_E
	end
end

% Initialisation de la matrice contenant des valeurs differentes pour chaque E :
etiquette = zeros(size(I));

for k = 1:length(liste_E)
    
    % Passage en indices lineaires pour remplir la matrice "etiquette" :
	E = liste_E{k};
	indices_E = sub2ind(size(I),E(:,1),E(:,2));
	etiquette(indices_E) = k;
    
end

% Affichage des ensembles E :
% (la fonction label2rgb donne a chaque ensemble E une couleur differente)
I_resultat = label2rgb(etiquette,'parula',[0.5,0.5,0.5]);
subplot(1,3,3);
    imagesc(I_resultat);
    axis image off;
    title('Ensembles candidats','FontSize',30);

save exercice_1;
