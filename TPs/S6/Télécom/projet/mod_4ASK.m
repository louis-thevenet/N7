clear all
close all
addpath(genpath("./fig2svg"));

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                   PROJET TÉLÉCOM/SIGNAL                                        %
%      Étude d'une chaîne de transmission sur porteuse pour une transmission satellite fixe      %
%                   THEVENET Louis & LÉCUYER Simon 1A SN ENSEEIHT 2023/2024                      %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% PARAMETRES GENERAUX
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
Nb = 3000;       % Nombre de bits générés
Fe = 6000;       % Fréquence d'échantillonnage en Hz
Te = 1 / Fe;     % Période d'échantillonnage en secondes
Rb = 3000;       % Débit binaire en bits par seconde
Tb = 1 / Rb;     % Période binaire
Fp = 2000;       % Fréquence porteuse

% Génération de bits aléatoires
bits = randi([0, 1], 1, Nb);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% MODULATEUR 4-ASK
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Paramètres du Modulateur
M = 4;                    % Ordre de modulation
Ts = Tb * log2(M);        % Période symbole
Rs = 1/Ts;                % Débit symbole
Ns = Ts/Te;               % Nombre d'échantillons par symbole
Nsb = Nb / log2(M);       % Nombre de symboles
alpha = 0.35;             % Facteur de roll-off
L = 6;                    % Longueur du filtre en durées de symboles
h = rcosdesign(alpha, L, Ns);  % Filtre en cosinus surélevé

% Conversion du signal en symboles
symboles = zeros(1, Nsb);
for i = 1:Nsb
    symboles(i) = bi2de(bits((i-1)*2+1:i*2), 'left-msb');
end

% Mapping des symboles
symboles_mapped = pammod(symboles, M);

% Suréchantillonnage
symboles_sur_echantillonnes = kron(symboles_mapped, [1 zeros(1, Ns-1)]);

% Filtrage de mise en forme
signal_module = filter(h, 1, symboles_sur_echantillonnes);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% INTRODUCTION DU BRUIT
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
Px = mean(abs(signal_module).^2);

% Rapport signal à bruit par bit à l'entrée du récepteur (en dB)
EbN0dB = 6;
EbN0 = 10.^(EbN0dB ./ 10);

% Calcul de la variance du bruit 
sigma2 = (Px * Ns) ./ (2 * log2(M) * 10.^(EbN0dB/10));

% Génération du bruit
bruit = sqrt(sigma2') .* randn(length(EbN0), length(signal_module));

% Signal bruité
signal_bruite = signal_module + bruit;


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% TRACÉS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Démodulation
signal_recupere = filter(h, 1, signal_bruite);

% Échantillonnage pour extraire les symboles individuels
signal_echantillonne = signal_recupere(L:Ns:end);  % L est la longueur du filtre

% Démodulation des symboles échantillonnés
symboles_recuperes = pamdemod(signal_echantillonne, M);

% Tracé des constellations en sortie du mapping
figure('Name', 'Constellations en sortie du mapping - 4-ASK');
plot(real(symboles_mapped), imag(symboles_mapped), 'o');
xlabel('Partie réelle');
ylabel('Partie imaginaire');
title('Constellations en sortie du mapping - 4-ASK');

% Tracé des constellations en sortie de l’échantillonneur
figure('Name', 'Constellations en sortie de l’échantillonneur - 4-ASK');
plot(real(signal_echantillonne), imag(signal_echantillonne), 'o');
xlabel('Partie réelle');
ylabel('Partie imaginaire');
title('Constellations en sortie de l’échantillonneur - 4-ASK');


