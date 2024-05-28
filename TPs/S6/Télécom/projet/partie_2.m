%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                   PROJET TÉLÉCOM/SIGNAL                                        %
%      Étude d'une chaîne de transmission sur porteuse pour une transmission satellite fixe      %
%                   THEVENET Louis & LÉCUYER Simon 1A SN ENSEEIHT 2023/2024                      %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
clear all
close all
addpath(genpath("./fig2svg"));

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% PARAMÈTRES GÉNÉRAUX
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
Nb_bits = 3000;       % Nombre de bits générés
Fe = 24000;      % Fréquence d'échantillonnage en Hz
Te = 1/Fe;       % Période d'échantillonnage en secondes
Rb = 3000;       % Débit binaire en bits par seconde
Tb = 1/Rb;       % Période binaire
Fp = 2000;       % Fréquence porteuse

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% GENERATION D'UNE INFORMATION BINAIRE ALEATOIRE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

bits = randi([0,1], 1, Nb_bits);

% Tracé du signal binaire généré
% 2.1
figure('Name','Message à transmettre')
stem(bits, 'filled')
title("Message généré")
fig2svg("rapport/assets/2_message.svg");

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% MODULATEUR QPSK
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Paramètres du Modulateur
M = 4;                    % Ordre de modulation
n = log2(M);               % Nombre de bits par symbole
Ts = Tb * n;        % Période symbole
Rs = 1/Ts;                % Débit symbole
Ns = Ts/Te;               % Nombre d'échantillons par symbole
Nsb = Nb_bits / n;       % Nombre de symboles
alpha = 0.35;             % Facteur de roll-off
L = 6;                    % Longueur du filtre en durées de symboles

h = rcosdesign(alpha, L, Ns);  % Filtre en cosinus surélevé

% Mapping QPSK
mapping = [-1-1i, -1+1i, 1-1i, 1+1i];        %mapping constellation QPSK

%génération des symboles complexes dk
dk = mapping(bin2dec(int2str([bits(1:2:Nb_bits-1)', bits(2:2:Nb_bits)']))+1);

% Suréchantillonnage des bits
diracs = kron(dk,[1 zeros(1,Ns-1)]);

% Génération de l'enveloppe complexe associée au signal à transmettre
xe = filter(h,1,diracs);

I = real(xe);       %voie en phase
Q = imag(xe);       %voie en quadrature

Echelle_Temporelle = 0:Te:(length(xe)-1)*Te; % Echelle temporelle

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
x = real(xe.*exp(1i*2*pi*Fp*Echelle_Temporelle));

%2.2
subplot(3,1,3)
plot(Echelle_Temporelle, x)
xlabel("Temps (s)")
ylabel("x(t)")
title("Signal transmis sur fréquence porteuse")
fig2svg("rapport/assets/2_signal.svg");


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% DSP (Densité Spectrale de Puissance)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%2.3
% Calcul de la DSP du signal transmis sur fréquence porteuse
[S_x] = pwelch(x, [], [], [], Fe, 'twosided');

% Échelle de fréquence
taille_S_x = length(S_x);
Echelle_Frequentielle = (-taille_S_x/2:taille_S_x/2-1)*Fe/taille_S_x;

figure('Name','DSP')
semilogy(Echelle_Frequentielle, fftshift(S_x), 'b')
xline(Fp,'k', LineWidth=0.7, LineStyle='-.')
text(Fp, 10^(-10), 'f_p')
xline(-Fp,'k', LineWidth=0.7, LineStyle='-.');
text(-Fp, 10^(-10), '-f_p')
grid on
[~, legendIcons] = legend('DSP');
xlabel('Fréquences (Hz)')
ylabel('DSP')
title('Tracé de la DSP du signal transmis sur fréquence porteuse')
fig2svg("rapport/assets/2_dsp.svg", '', '', legendIcons);

%2.4
%EXPLICATION DE LA DSP


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% CALCUL DU TEB EN FONCTION DE E_b/N_0
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Génération du filtre de réception adapté
hr = fliplr(h);

% Prise en compte du retard introduit par le filtrage
retard = (length(h) - 1)/2 + (length(hr) - 1)/2;

% Instant d'échantillonnage.
n0=1;

EbN0dB = (0:0.2:6);                               %choix de Eb/N0
TEBS = zeros(1, length(EbN0dB));                  %tableau des TEB calculés

% Pourcentage d'erreur voulu sur la mesure du TEB
epsilon = 0.05;

for i = 1:length(EbN0dB)
    nbr_erreurs = 0;
    N = length(bits);
    while nbr_erreurs < 1/(epsilon^2)       %tant que le nombre d'erreurs est trop petit pour obtenir epsilon

        xe = filter(h,1,diracs);
        t = (0:Te:(length(xe)-1)*Te);
        x = real(xe.*exp(1i*2*pi*Fp*t));

        % Introduction du bruit
        Px = mean(abs(x).^2);
        Pn = Px*Ns/(2*n*10^(EbN0dB(i)/10));
        bruit = sqrt(Pn)*randn(1,length(x));
        x_bruite = x + bruit;

        % Retour en bande de base
        z1 = filter(hr, 1, x_bruite.* cos(2*pi*Fp*t));
        z2 = filter(hr, 1, x_bruite.* sin(2*pi*Fp*t));

        % Échantillonnage à n0+mNs en prenant en compte le retard induit
        zm1 = z1(retard+n0:Ns:end);
        zm2 = z2(retard+n0:Ns:end);

        % Décisions sur les symboles
        am1 = sign(zm1);
        am2 = -sign(zm2);

        % Demapping
        bm=[(am1+1)/2; (am2+1)/2];
        bm = bm(:)';

        % Calcul du TEB
        nbr_erreurs = length(find((bm-bits(1:length(bm))) ~=0));
        TEBS(i) = nbr_erreurs/length(bm);

        new_bits = randi([0,1],1,Nb_bits);       %ajout de Nb_bits bits;
        bits = [bits, new_bits];
        N = N + Nb_bits;
        dk = [dk, mapping(bin2dec(int2str([new_bits(1:2:(Nb_bits-1))', ...
                                           new_bits(2:2:Nb_bits)']))+1)];
        diracs = kron(dk,[1 zeros(1,Ns-1)]);
    end


end


% TEB théorique
%2.6
EbN0 = 10.^(EbN0dB ./ 10);
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
fig2svg("rapport/assets/2_teb.svg", '', '', legendIcons);

%Sauvegarde du tableau des TEB pour la comparaison avec la partie 3
save('TEB_partie_2', 'TEBS');

%2.6

%Implanter la chaîne passe-bas équivalente présente plusieurs avantages :

%1. Simplification des Calculs : Les opérations se font en bande de base à des fréquences plus basses, simplifiant ainsi les calculs.
%2. Réduction de la Charge de Traitement : Moins d'échantillons sont nécessaires car la fréquence d'échantillonnage est plus basse que celle en bande passante.
%3. Modulation et Démodulation Simplifiées : Les symboles complexes peuvent être traités directement sans multiplication par des sinusoïdes à haute fréquence.
%4. Analyse Spectrale et Filtrage : L'analyse de la DSP et la conception des filtres sont plus directes et intuitives en bande de base.

%En résumé, la chaîne passe-bas équivalente permet une conception plus
%simple et une réduction de la complexité de traitement.


