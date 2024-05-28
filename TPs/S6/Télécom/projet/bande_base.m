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
%% INTRODUCTION DU BRUIT
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Rapport signal à bruit par bit à l'entrée du récepteur (en dB)
EbN0dB = 0:6;
EbN0 = 10.^(EbN0dB ./ 10);

% Calcul de la variance du bruit complexe
sigma2 = (Px * Ns) ./ (2 * log2(M) * 10.^(EbN0dB/10));

% Génération du bruit complexe

bruit_I = sqrt(sigma2') .* randn(length(EbN0), length(x_baseband));
bruit_Q = sqrt(sigma2') .* randn(length(EbN0), length(x_baseband));

% Signal bruité
x_bruit = x_baseband + bruit_I + 1i * bruit_Q;

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% TRACÉS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Tracé des signaux générés sur les voies en phase et en quadrature
%2.1
figure('Name', 'Signaux Générés/Transmis - Bande de Base');
subplot(2, 1, 1);
plot(temps_phase, real(x_bruit));
xlabel('Temps (s)');
ylabel('I(t)');
title('Signal généré sur la voie en phase (Bande de Base)');

subplot(2, 1, 2);
plot(temps_phase, imag(x_bruit));
xlabel('Temps (s)');
ylabel('Q(t)');
title('Signal généré sur la voie en quadrature (Bande de Base)');
[~, legendIcons] = legend('Signal généré sur la voie en phase', 'Signal généré sur la voie en quadrature');
fig2svg("rapport/assets/3_signal.svg", '','', legendIcons);

% Tracé de la densité spectrale de puissance de l'enveloppe complexe
%2.2
figure('Name', 'DSP de l''enveloppe complexe - Bande de Base');
X_baseband = fft(x_baseband);
echelle_frequentielle = linspace(-Fe/2, Fe/2, length(X_baseband));
semilogy(echelle_frequentielle, fftshift(abs(X_baseband).^2 / length(X_baseband)));
grid;
xlabel('Fréquences (Hz)');
ylabel('DSP');
title('DSP de l''enveloppe complexe (Bande de Base)');
[~, legendIcons] = legend("DSP de l\'enveloppe complexe - Bande de Base");
fig2svg("rapport/assets/3_dsp.svg", '','', legendIcons);

constellation_dk = dk; % Garder la constellation de départ


% Constellation des symboles modulés
%2.5
figure('Name', ['Constellations - Mapping  ']);
plot(constellation_dk, 'bo'); % Constellation des symboles modulés
xlabel('Partie réelle');
ylabel('Partie imaginaire');
title(['Constellation des symboles modulés']);
grid on;
[~, legendIcons] = legend("Constellation des symboles modulés");
fig2svg("rapport/assets/3_constellation.svg", '','', legendIcons);

% Plage de valeurs Eb/N0
EbN0dB_range = 0:2:6;
EbN0_range = 10.^(EbN0dB_range / 10);


% Boucle sur les valeurs Eb/N0
for i = 1:length(EbN0_range)
    % Générer le signal bruité
    bruit_I = sqrt(sigma2(i)) * randn(1, length(x_baseband));
    bruit_Q = sqrt(sigma2(i)) * randn(1, length(x_baseband));

    x_bruit = x_baseband + bruit_I + 1i * bruit_Q;


      %Signal demodulé par le filtre de reception (meme que celui de mise en forme)
    z = filter(h,1,x_bruit);

    %décalage avec l'instant optimal
    z_decalage = z(length(h):Ns:end);

    % Constellation des symboles reçus après échantillonnage
    %2.5
    figure('Name', ['Constellations - Échantillonneur - Eb/N0 = ' num2str(EbN0dB_range(i)) ' dB']);
    plot(real(z_decalage), imag(z_decalage), 'bo'); % Constellation des symboles reçus
    xlabel('Partie réelle');
    ylabel('Partie imaginaire');
    title(['Constellation des symboles reçus - Eb/N0 = ' num2str(EbN0dB_range(i)) ' dB']);
    [~, legendIcons] = legend(['Constellation des symboles reçus - Eb/N0 = ' num2str(EbN0dB_range(i)) ' dB']);
    fig2svg("rapport/assets/3_constellation_"+num2str(EbN0dB_range(i))+".svg", '','', legendIcons);
    grid on;
end


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% TEB SIMULÉ/THÉORIQUE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Calcul et tracé du TEB
% Comparaison du TEB simulé avec le TEB théorique
%3.5

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

TEBS = mean(xr_matrix ~= bits(1:2*num_symbols), 2);


% TEB théorique
%3.6
TEBT = qfunc(sqrt(2 * EbN0));
TEST = 2 * TEBT;

% Tracé
%3.6
figure('Name','Comparaison du TEB simulé/théorique')
semilogy(EbN0dB, TEBT, 'r', 'LineWidth', 3)
hold on
semilogy(EbN0dB, TEBS, 'gd', 'LineWidth', 3)
grid
[~, legendIcons] = legend('TEB théorique', 'TEB simulé');
xlabel('Eb/N0 (dB)')
title('Tracé des TEB du signal')
fig2svg("rapport/assets/3_comparaison_teb.svg", '', '', legendIcons);
