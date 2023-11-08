clear;
close all;
clc;

% Recuperation de la taille de l'ecran pour afficher les figures
taille_ecran = get(0,'ScreenSize');
L = taille_ecran(3);
H = taille_ecran(4);

% Lecture d'une image interne a Matlab et conversion en niveaux de gris et en doubles :
I = double(rgb2gray(imread('autumn.tif')));

% Calcul de l'histogramme normalise de l'image d'origine :
[vecteurs_frequences,vecteur_Imin_a_Imax] = histogramme_normalise(I); % FONCTION A CODER

% Affichage de l'histogramme normalise de l'image d'origine :
figure('Position',[0.05*L,0.1*H,0.9*L,0.7*H]);
subplot(2,2,1)
    imagesc(0:255,0:1.1*max(vecteurs_frequences),0:255)
    colormap gray
    axis xy
    hold on
    plot(vecteur_Imin_a_Imax,vecteurs_frequences,'r.','LineWidth',2);
    axis([0 255 0 1.1*max(vecteurs_frequences)]);
    xlabel('Niveau de gris');
    ylabel('Frequence');
    set(gca,'FontSize',20);
    title('Histogramme normalise de l''image d''origine')

% Codage de Huffman de l'image d'origine :
[I_encodee,dictionnaire] = encodage_image(I); % FONCTION A CODER
nb_symboles = size(dictionnaire,1);
liste_symboles = zeros(nb_symboles,1);
longueur_symboles = zeros(nb_symboles,1);
for k = 1:nb_symboles
    liste_symboles(k) = dictionnaire{k,1};
    longueur_symboles(k) = length(dictionnaire{k,2});
end

% Calcul du coefficient de compression obtenu par le codage de Huffman :
coeff_compression_avant_decorrelation = coefficient_compression(I(:),I_encodee); % FONCTION A CODER

% Affichage du nombre de bits par symbole pour l'image d'origine :
subplot(2,2,3)
    imagesc(0:255,0:1.1*max(longueur_symboles),0:255)
    colormap gray
    axis xy
    hold on
    plot(liste_symboles,longueur_symboles,'r.','LineWidth',2);
    axis([0 255 0 1.1*max(longueur_symboles)]);
    xlabel('Niveau de gris');
    ylabel('Nb bits/symbole');
    set(gca,'FontSize',20);
    title(['Repartition des bits/symbole (Coef Comp = ' num2str(coeff_compression_avant_decorrelation,'%.2f') ')'])

% Calcul de l'image decorrelee :
I_decorrelee = decorrelation_colonnes(I); % FONCTION A CODER

% Calcul de l'histogramme normalise de l'image decorrelee : 
[vecteurs_frequences,vecteur_Imin_a_Imax] = histogramme_normalise(I_decorrelee); % FONCTION A CODER

% Affichage de l'histogramme normalise de l'image decorrelee :
subplot(2,2,2)
    imagesc(-255:255,0:1.1*max(vecteurs_frequences),-255:255)
    colormap gray
    axis xy
    hold on
    plot(vecteur_Imin_a_Imax,vecteurs_frequences,'r.','LineWidth',2);
    axis([-255 255 0 1.1*max(vecteurs_frequences)]);
    xlabel('Niveau de gris');
    ylabel('Frequence');
    set(gca,'FontSize',20);
    title('Histogramme normalise de l''image decorrelee')

% Codage de Huffman de l'image decorrelee :
[I_encodee,dictionnaire] = encodage_image(I_decorrelee); % FONCTION A CODER
nb_symboles = size(dictionnaire,1);
liste_symboles = zeros(nb_symboles,1);
longueur_symboles = zeros(nb_symboles,1);
for k = 1:nb_symboles
    liste_symboles(k) = dictionnaire{k,1};
    longueur_symboles(k) = length(dictionnaire{k,2});
end

% Calcul du coefficient de compression obtenu par decorrelation prealable au codage de Huffman :
coeff_compression_apres_decorrelation = coefficient_compression(I_decorrelee(:),I_encodee); % FONCTION A CODER

% Affichage du nombre de bits par symbole pour l'image decorrelee :
subplot(2,2,4)
    imagesc(-255:255,0:1.1*max(longueur_symboles),-255:255)
    colormap gray
    axis xy
    hold on
    plot(liste_symboles,longueur_symboles,'r.','LineWidth',2);
    axis([-255 255 0 1.1*max(longueur_symboles)]);
    xlabel('Niveau de gris');
    ylabel('Nb bits/symbole');
    set(gca,'FontSize',20);
    title(['Repartition des bits/symbole (Coef Comp = ' num2str(coeff_compression_apres_decorrelation,'%.2f') ')'])
