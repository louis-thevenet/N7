clear all
close all
addpath(genpath("./fig2svg"));
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                   PROJET TÉLÉCOM/SIGNAL                                        %
%      Étude d'une chaîne de transmission sur porteuse pour une transmission satellite fixe      %
%                   THEVENET Louis & LÉCUYER Simon 1A SN ENSEEIHT 2023/2024                      %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% PARAMÈTRES GÉNÉRAUX
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
Nb = 50000;       % Nombre de bits générés
Fe = 24000;      % Fréquence d'échantillonnage en Hz
Te = 1/Fe;       % Période d'échantillonnage en secondes
Rb = 3000;       % Débit binaire en bits par seconde
Tb = 1/Rb;       % Période binaire
Fp = 2000;       % Fréquence porteuse

% Suite de bits / Information à transmettre
bits = randi([0,1], 1, Nb);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% MODULATEUR QPSK
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

% Mapping QPSK
dk = 1 - 2*bits(1:2:Nb) + 1i*(1-2*bits(2:2:Nb));

% Suréchantillonnage des bits
suite_diracs_ak = kron(real(dk), [1 zeros(1, Ns-1)]);
suite_diracs_bk = kron(imag(dk), [1 zeros(1, Ns-1)]);

% Filtrage
I = filter(h, 1, suite_diracs_ak);
Q = filter(h, 1, suite_diracs_bk);
temps_phase = 0:Te:(length(I)-1)*Te;

x = real((I + Q*1i) .* exp(2*pi*1i*Fp*temps_phase));

Echelle_Temporelle = 0:Te:(length(x)-1)*Te;


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% TEB SIMULÉ QPSK
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
Px = mean(abs(x).^2);

% Calcul du TEB simulé pour différentes valeurs de Eb/N0
EbN0dB = 0:0.2:6;
EbN0 = 10.^(EbN0dB ./ 10);

% Utilisation de vecteurs pour le calcul
sigma2_vals = (Px * Ns) ./ (2 * log2(M) * EbN0);
bruits = sqrt(sigma2_vals') .* randn(length(EbN0), length(x));
rs = x + bruits;

ys = rs .* cos(2*pi*Fp*Echelle_Temporelle) - 1i * rs .* sin(2*pi*Fp*Echelle_Temporelle);
zs = filter(h, 1, ys')';

% Ajustement de la taille pour correspondre au nombre de symboles
num_symbols = floor((length(zs) - length(h)) / Ns);
z_decalages = zs(:, length(h):Ns:(length(h) + Ns*num_symbols - 1));

% Détection de seuil
xr_reals = real(z_decalages) < 0;
xr_imags = imag(z_decalages) < 0;

xr_matrix = zeros(length(EbN0), 2*num_symbols);
xr_matrix(:, 1:2:end) = xr_reals;
xr_matrix(:, 2:2:end) = xr_imags;

TEBS_2 = mean(xr_matrix ~= bits(1:2*num_symbols), 2);



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% PARAMETRES GENERAUX
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
Nb = 50000;       % Nombre de bits générés
Fe = 6000;       % Fréquence d'échantillonnage en Hz
Te = 1 / Fe;     % Période d'échantillonnage en secondes
Rb = 3000;       % Débit binaire en bits par seconde
Tb = 1 / Rb;     % Période binaire
Fp = 2000;       % Fréquence porteuse

% Génération de bits aléatoires
bits = randi([0, 1], 1, Nb);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% MODULATEUR QPSK
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Paramètres du Modulateur
M = 4;
Ts = Tb * log2(M);  % Période symbole
Rs = 1 / Ts;         % Débit symbole
Ns = Ts / Te;
Nsb = Nb / log2(M);
alpha = 0.35; % Roll-off factor
L = 6;
h = rcosdesign(alpha, L, Ns);

% Mapping QPSK
dk = 1 - 2 * bits(1:2:Nb) + 1i * (1 - 2 * bits(2:2:Nb));


% Surréchantillonnage des bits
suite_diracs_ak = kron(real(dk), [1 zeros(1, Ns - 1)]);
suite_diracs_bk = kron(imag(dk), [1 zeros(1, Ns - 1)]);

% Filtrage
I = filter(h, 1, suite_diracs_ak);
Q = filter(h, 1, suite_diracs_bk);
temps_phase = 0:Te:(length(I) - 1) * Te;

% Signal en bande de base
x_baseband = (I + Q * 1i);

% Puissance moyenne du signal
Px = mean(abs(x_baseband).^2);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% TEB SIMULÉ
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


% Calcul du TEB simulé pour différentes valeurs de Eb/N0
EbN0dB = 0:0.2:6;
EbN0 = 10.^(EbN0dB ./ 10);

% Utilisation de vecteurs pour le calcul
sigma2_vals = (Px * Ns) ./ (2 * log2(M) * EbN0);
bruits_I = sqrt(sigma2_vals') .* randn(length(EbN0), length(x_baseband));
bruits_Q = sqrt(sigma2_vals') .* randn(length(EbN0), length(x_baseband));

rs = x_baseband + bruits_I + 1i * bruits_Q;
zs = filter(h, 1, rs')';

% Ajustement de la taille pour correspondre au nombre de symboles
num_symbols = floor((length(zs) - length(h)) / Ns);
z_decalages = zs(:, length(h):Ns:(length(h) + Ns*num_symbols - 1));

% Détection de seuil
xr_reals = real(z_decalages) < 0;
xr_imags = imag(z_decalages) < 0;

xr_matrix = zeros(length(EbN0), 2*num_symbols);
xr_matrix(:, 1:2:end) = xr_reals;
xr_matrix(:, 2:2:end) = xr_imags;

TEBS_3 = mean(xr_matrix ~= bits(1:2*num_symbols), 2);






% Tracé
%2.6
figure('Name','Comparaison des TEB transmission avec transposition de fré́quence et chaine équivalente passe-bas')

semilogy(EbN0dB, TEBS_2, 'r', 'LineWidth', 3)
hold on
semilogy(EbN0dB, TEBS_3, 'g', 'LineWidth', 3)
grid
[~, legendIcons] = legend('TEB transmission avec transposition de fré́quence', 'TEB Chaine passe-bas équivalente');
xlabel('Eb/N0 (dB)')
title('Tracé des TEB du signal')
fig2svg("rapport/assets/3_6_comparaison_teb.svg", '', '', legendIcons);



