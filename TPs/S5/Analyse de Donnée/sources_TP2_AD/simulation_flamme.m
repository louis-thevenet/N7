clear;
close all;
clc;

taille_ecran = get(0,'ScreenSize');
L = taille_ecran(3);
H = taille_ecran(4);

% Chargement et initialisations :
load donnees;
load parametres_moments;
load texture;
beta_0 = bord_inf(1,1);
gamma_0 = bord_sup(1,1);

% Simulation d'une flamme de bougie :
figure('Name','Simulation d''une flamme de bougie',...
	   'Position',[0.1*L,0.1*H,0.8*L,0.7*H],...
       'Color',[0.7 0.75 0.85]);

% Affichage de la texture d'origine
subplot(1,2,1)
    imagesc(texture)
    axis image off;
    colormap(hot);
    title('Texture de depart')
    set(gca,'FontSize',20);
   
l_image = 1000;					        % Largeur de l'image
h_image = 1000;					        % Hauteur de l'image
h_flamme = round(0.85*h_image);			% Hauteur de la flamme
x = transpose(0:1/(h_flamme-1):1);		% Abscisses normalisees entre 0 et 1
nb_images = 100;				        % Longueur de la sequence
[nb_lignes,nb_colonnes] = size(texture);
for j = 1:nb_images
    
    % Tirages aleatoires des silouhettes :
    [y_inf,y_sup] = generation_aleatoire_courbe(x,moyennes,ecarts_types,beta_0,gamma_0); % FONCTION A CODER

    % Affichage des flammes :
    I = zeros(h_image,l_image);
    if sum(y_inf<y_sup)==0
        for ligne = 1:h_flamme
            ligne_texture = round((nb_lignes*(h_flamme-ligne)+ligne-1)/(h_flamme-1));
            colonne_min = floor(l_image/2+(y_sup(ligne)-(beta_0+gamma_0)/2)*l_image/150);
            colonne_max = ceil(l_image/2+(y_inf(ligne)-(beta_0+gamma_0)/2)*l_image/150);
            largeur_flamme = colonne_max-colonne_min;
            for colonne = max(colonne_min,1):min(colonne_max,l_image)
                colonne_texture = round((colonne-colonne_min)*(nb_colonnes-1)/largeur_flamme+1);
                I(ligne,colonne) = round(255*texture(ligne_texture,colonne_texture));
            end
        end
        subplot(1,2,2)
            imagesc(I);
            axis image xy off;
            colormap(hot);
            title('Generation de flamme');
            set(gca,'FontSize',20);

        pause(0.2);
    end
end
