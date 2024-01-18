clear;
close all;
clc;

exercice_2;

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
figure('Position',[0.05*L,0.1*H,0.9*L,0.3*H]);
subplot(1,2,1)
    imagesc(0:255,0:1.1*max(longueur_symboles),0:255)
    colormap gray
    axis xy
    hold on
    plot(liste_symboles,longueur_symboles,'r.','LineWidth',2);
    axis([0 255 0 1.1*max(longueur_symboles)]);
    xlabel('Niveau de gris');
    ylabel('Nb bits/symbole');
    set(gca,'FontSize',15);
    title(['Repartition des bits/symbole (Coef Comp = ' num2str(coeff_compression_avant_decorrelation,'%.2f') ')'])

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
subplot(1,2,2)
    imagesc(-255:255,0:1.1*max(longueur_symboles),-255:255)
    colormap gray
    axis xy
    hold on
    plot(liste_symboles,longueur_symboles,'r.','LineWidth',2);
    axis([-255 255 0 1.1*max(longueur_symboles)]);
    xlabel('Niveau de gris');
    ylabel('Nb bits/symbole');
    set(gca,'FontSize',15);
    title(['Repartition des bits/symbole (Coef Comp = ' num2str(coeff_compression_apres_decorrelation,'%.2f') ')'])
