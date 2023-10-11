clear;
close all;
clc;

% Recuperation de la taille de l'ecran pour afficher les figures
taille_ecran = get(0,'ScreenSize');
L = taille_ecran(3);
H = taille_ecran(4);

% Lecture d'une image interne a Matlab et conversion en niveaux de gris et en doubles :
I = double(rgb2gray(imread('autumn.tif')));

% Calcul de l'image decorrelee :
I_decorrelee = decorrelation_colonnes(I); % FONCTION A CODER

% Codage de Huffman de l'image decorrelee :
[I_encodee,dictionnaire,hauteur_I,largeur_I] = encodage_image(I_decorrelee); % FONCTION A CODER

% Calcul de l'image recorrelee :
I_reconstruite = reconstruction_image(I_encodee,dictionnaire,hauteur_I,largeur_I); % FONCTION A CODER

% Erreur de reconstruction :
I_erreur = I_reconstruite-I;
norme_erreur_reconstruction_pixellique = mean(mean(abs(I_erreur)));

% Affichage de l'image d'origine :
figure('Position',[0.1*L,0.1*H,0.8*L,0.7*H]);
subplot(2,2,1)
    imagesc(I);
    axis image off;
    colormap gray;
    set(gca,'FontSize',20);
    title('Image d''origine')
    
% Affichage de l'image reconstruite :    
subplot(2,2,2)
    imagesc(I_reconstruite);
    axis image off;
    colormap gray;
    set(gca,'FontSize',20);
    title('Image reconstruite')
    
% Affichage de l'image d'erreur :    
subplot(2,1,2)
    imagesc(I_erreur);
    axis image off;
    colormap gray;
    set(gca,'FontSize',20);
    title(['Image d''erreur (norme = ' num2str(norme_erreur_reconstruction_pixellique,'%.2f') ')'])
    