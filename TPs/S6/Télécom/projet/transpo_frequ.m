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
Nb = 5000;       % Nombre de bits générés
Fe = 24000;      % Fréquence d'échantillonnage en Hz
Te = 1/Fe;       % Période d'échantillonnage en secondes
Rb = 3000;       % Débit binaire en bits par seconde
Tb = 1/Rb;       % Période binaire
Fp = 2000;       % Fréquence porteuse

% Suite de bits / Information à transmettre
bits = randi([0,1], 1, Nb);

% Tracé du signal binaire généré
% 2.1
figure('Name','Message à transmettre')
stem(bits, 'filled')
title("Message généré")
fig2svg("2_message.svg");

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

% Tracés des Signaux Générés/Transmis
figure('Name','Signaux Générés/Transmis')

% Signal sur la voie en phase
%2.1
subplot(3,1,1)
plot(Echelle_Temporelle, I)
xlabel("Temps (s)")
ylabel("I(t)")
title("Signal généré sur la voie en phase")

% Signal sur la voie en quadrature
%2.1
subplot(3,1,2)
plot(Echelle_Temporelle, Q)
xlabel("Temps (s)")
ylabel("Q(t)")
title("Signal généré sur la voie en quadrature")

% Signal transmis sur fréquence porteuse
%2.2
subplot(3,1,3)
plot(Echelle_Temporelle, x)
xlabel("Temps (s)")
ylabel("x(t)")
title("Signal transmis sur fréquence porteuse")
fig2svg("2_signal.svg");

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% DSP (Densité Spectrale de Puissance)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%2.3
X= fft(x, 512);

echelle_frequentielle = linspace(-Fe/2, Fe/2, length(X));

figure('Name','DSP')
semilogy(echelle_frequentielle, fftshift(abs(X).^2/length(X)), 'b')
grid
[~, legendIcons] = legend('DSP');
xlabel('Fréquences (Hz)')
ylabel('DSP')
title('Tracé de la DSP du signal transmis sur fréquence porteuse')
fig2svg("2_dsp.svg", '', '', legendIcons);

%2.4
%TODO : EXPLICATION DE LA DSP

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% INTRODUCTION DU BRUIT
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
SNR = 10;  % (Eb/N0)

Px = mean(abs(x).^2);
sigma2 = (Px * Ns) / (2 * log2(M) * SNR);
bruit = sqrt(sigma2) * randn(1, length(x));

r = x + bruit;  % Signal bruité

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% DÉMODULATEUR
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Signal auquel on enlève la fréquence porteuse
y = r .* cos(2*pi*Fp*Echelle_Temporelle) - 1i * r .* sin(2*pi*Fp*Echelle_Temporelle);

% Signal démodulé par le filtre de réception (même que celui de mise en forme)
z = filter(h, 1, y);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% DIAGRAMME DE L'ŒIL
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
eyediagram(z, 2*Ns, 2*Ns)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% TEB SIMULÉ/THÉORIQUE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Calcul et tracé du TEB
% Comparaison du TEB simulé avec le TEB théorique
%2.5

% TEB simulé
% Décalage avec l'instant optimal
z_decalage = z(length(h):Ns:end);

% Détection de seuil
xr = zeros(1, Nb);
xr(1:2:Nb-2*L) = (real(z_decalage) < 0);
xr(2:2:Nb-2*L) = (imag(z_decalage) < 0);

% Taux d'erreur binaire
TEB = mean(xr ~= bits);

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

TEBS = mean(xr_matrix ~= bits(1:2*num_symbols), 2);


% TEB théorique
%2.6
TEBT = qfunc(sqrt(2 * EbN0));
TEST = 2 * TEBT;

% Tracé
%2.6
figure('Name','Comparaison du TEB simulé/théorique')
semilogy(EbN0dB, TEBT, 'r', 'LineWidth', 3)
hold on
semilogy(EbN0dB, TEBS, 'gd', 'LineWidth', 3)
grid
[~, legendIcons] = legend('TEB théorique', 'TEB simulé');
xlabel('Eb/N0 (dB)')
title('Tracé des TEB du signal')
fig2svg("2_comparaison_teb.svg", '', '', legendIcons);

%2.6

%Implanter la chaîne passe-bas équivalente présente plusieurs avantages :

%1. Simplification des Calculs : Les opérations se font en bande de base à des fréquences plus basses, simplifiant ainsi les calculs.
%2. Réduction de la Charge de Traitement : Moins d'échantillons sont nécessaires car la fréquence d'échantillonnage est plus basse que celle en bande passante.
%3. Modulation et Démodulation Simplifiées : Les symboles complexes peuvent être traités directement sans multiplication par des sinusoïdes à haute fréquence.
%4. Analyse Spectrale et Filtrage : L'analyse de la DSP et la conception des filtres sont plus directes et intuitives en bande de base.

%En résumé, la chaîne passe-bas équivalente permet une conception plus
%simple et une réduction de la complexité de traitement.


