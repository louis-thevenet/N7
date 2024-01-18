clear;
close all;
clc;

taille_ecran = get(0,'ScreenSize');
L = taille_ecran(3);
H = taille_ecran(4);

% Chemin d'acces aux images :
chemin = './Donnees/';

%--------------------------------------------------------------------------
% Images de pensees
%--------------------------------------------------------------------------

% Lecture des images de pensees :
fichier = [chemin 'pensees'];
s = whos('-file',fichier);
nb_pensees = length(s);
load(fichier);

% Affichage des images de pensees :
fact = factor(nb_pensees);
nb_lignes_affichage = fact(2);
nb_colonnes_affichage = fact(1);
figure('Name','Images de pensees',...
       'Position',[0.02*L,0.1*H,0.3*L,0.7*H],...
       'Color',[0.7 0.75 0.85]);
for i = 1:nb_pensees
	subplot(nb_lignes_affichage,nb_colonnes_affichage,i);
	imagesc(eval(['pe' num2str(i)]));
	title(['Pensee n°' num2str(i)],'FontSize',12);
	axis off image;
end


%--------------------------------------------------------------------------
% Images d'oeillets
%--------------------------------------------------------------------------

% Lecture des images d'oeillets :
fichier = [chemin 'oeillets'];
s = whos('-file',fichier);
nb_oeillets = length(s);
load(fichier);

% Affichage des images d'oeillets :
fact = factor(nb_oeillets);
nb_lignes_affichage = fact(2);
nb_colonnes_affichage = fact(1);
figure('Name','Images d''oeillets',...
       'Position',[0.35*L,0.1*H,0.3*L,0.7*H],...
       'Color',[0.7 0.75 0.85]);
for i = 1:nb_oeillets
	subplot(nb_lignes_affichage,nb_colonnes_affichage,i);
	imagesc(eval(['oe' num2str(i)]));
	title(['Oeillet n°' num2str(i)],'FontSize',12);
	axis off image;
end

%--------------------------------------------------------------------------
% Images de chrysanthemes
%--------------------------------------------------------------------------

% Lecture des images de chrysanthemes :
fichier = [chemin 'chrysanthemes'];
s = whos('-file',fichier);
nb_chrysanthemes = length(s);
load(fichier);

% Affichage des images de chrysanthemes :
fact = factor(nb_chrysanthemes);
nb_lignes_affichage = fact(2);
nb_colonnes_affichage = fact(1);
figure('Name','Images de chrysanthemes',...
       'Position',[0.68*L,0.1*H,0.3*L,0.7*H],...
       'Color',[0.7 0.75 0.85]);
for i = 1:nb_chrysanthemes
	subplot(nb_lignes_affichage,nb_colonnes_affichage,i);
	imagesc(eval(['ch' num2str(i)]));
	title(['Chrysantheme n°' num2str(i)],'FontSize',12);
	axis off image
end

clear chemin fact fichier i nb_lignes_affichage nb_colonnes_affichage s taille_ecran;
save donnees_exercice_1;
