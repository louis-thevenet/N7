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
Px_e = mean(abs(x_baseband).^2);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% INTRODUCTION DU BRUIT
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Rapport signal à bruit par bit à l'entrée du récepteur (en dB)
EbN0dB = 0:6;
EbN0 = 10.^(EbN0dB ./ 10);

% Calcul de la variance du bruit complexe
sigma2 = (Px_e * Ns) ./ (2 * log2(M) * 10.^(EbN0dB/10));

% Génération du bruit complexe

bruit_I = sqrt(sigma2') .* randn(length(EbN0), length(x_baseband));
bruit_Q = sqrt(sigma2') .* randn(length(EbN0), length(x_baseband));

% Signal bruité
x_bruit_I = x_baseband + bruit_I;
x_bruit_Q = x_baseband + bruit_Q;

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% TRACÉS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Tracé des signaux générés sur les voies en phase et en quadrature
%2.1
figure('Name', 'Signaux Générés/Transmis - Bande de Base');
subplot(2, 1, 1);
plot(temps_phase, real(x_bruit_I));
xlabel('Temps (s)');
ylabel('I(t)');
title('Signal généré sur la voie en phase (Bande de Base)');

subplot(2, 1, 2);
plot(temps_phase, imag(x_bruit_Q));
xlabel('Temps (s)');
ylabel('Q(t)');
title('Signal généré sur la voie en quadrature (Bande de Base)');

% Tracé de la densité spectrale de puissance de l'enveloppe complexe
%2.2
figure('Name', 'DSP de l''enveloppe complexe - Bande de Base');
X_baseband = fft(x_baseband);
echelle_frequentielle = linspace(-Fe/2, Fe/2, length(X_baseband));
plot(echelle_frequentielle, fftshift(abs(X_baseband).^2 / length(X_baseband)));
grid;
xlabel('Fréquences (Hz)');
ylabel('DSP');
title('DSP de l''enveloppe complexe (Bande de Base)');


constellation_dk = dk; % Garder la constellation de départ

% Plage de valeurs Eb/N0
EbN0dB_range = 0:6;
EbN0_range = 10.^(EbN0dB_range / 10);

% Initialiser les figures
figure('Name', 'Constellations - Mapping');
hold on;

figure('Name', 'Constellations - Échantillonneur');
hold on;

% Boucle sur les valeurs Eb/N0
for i = 1:length(EbN0_range)
    % Générer le signal bruité
    bruit_I = sqrt(sigma2(i)) * randn(1, length(x_baseband));
    bruit_Q = sqrt(sigma2(i)) * randn(1, length(x_baseband));
    x_bruit_I = x_baseband + bruit_I;
    x_bruit_Q = x_baseband + bruit_Q;
    
    % Constellation des symboles modulés
    %2.5
    figure('Name', ['Constellations - Mapping - Eb/N0 = ' num2str(EbN0dB_range(i)) ' dB']);
    plot(constellation_dk, 'bo'); % Constellation des symboles modulés
    xlabel('Partie réelle');
    ylabel('Partie imaginaire');
    title(['Constellation des symboles modulés - Eb/N0 = ' num2str(EbN0dB_range(i)) ' dB']);
    grid on;
    
    % Constellation des symboles reçus après échantillonnage
    %2.5
    figure('Name', ['Constellations - Échantillonneur - Eb/N0 = ' num2str(EbN0dB_range(i)) ' dB']);
    plot(real(x_bruit_I), imag(x_bruit_Q), 'bo'); % Constellation des symboles reçus
    xlabel('Partie réelle');
    ylabel('Partie imaginaire');
    title(['Constellation des symboles reçus - Eb/N0 = ' num2str(EbN0dB_range(i)) ' dB']);
    grid on;
end

% TODO(marche pas) : Calcul du TEB en fonction du rapport signal à bruit par bit (Eb/N0)
%2.6
TEB_simule = zeros(size(EbN0dB_range));
for i = 1:length(EbN0_range)
    % Générer le signal bruité
    bruit_I = sqrt(sigma2(i)) * randn(1, length(x_baseband));
    bruit_Q = sqrt(sigma2(i)) * randn(1, length(x_baseband));
    x_bruit_I = x_baseband + bruit_I;
    x_bruit_Q = x_baseband + bruit_Q;
    
    % Démodulation (détection du symbole le plus proche)
    symboles_rec_I = real(x_bruit_I) < 0;
    symboles_rec_Q = imag(x_bruit_Q) < 0;
    
    % Calcul du TEB
    TEB_simule(i) = mean((symboles_rec_I ~= real(dk)) | (symboles_rec_Q ~= imag(dk)));
end

% Tracé du TEB en fonction du rapport signal à bruit par bit (Eb/N0)
figure('Name', 'TEB Simulé en fonction de Eb/N0');
semilogy(EbN0dB_range, TEB_simule, 'b', 'LineWidth', 2);
grid on;
xlabel('Eb/N0 (dB)');
ylabel('TEB');
title('TEB Simulé en fonction de Eb/N0');

