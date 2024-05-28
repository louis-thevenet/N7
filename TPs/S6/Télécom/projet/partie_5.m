%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                   PROJET TÉLÉCOM/SIGNAL                                        %
%      Étude d'une chaîne de transmission sur porteuse pour une transmission satellite fixe      %
%                   THEVENET Louis & LÉCUYER Simon 1A SN ENSEEIHT 2023/2024                      %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
clear all
close all
addpath(genpath("./fig2svg"));

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% PARAMETRES GENERAUX
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
Nb_bits = 3000;       % Nombre de bits générés
Fe = 6000;       % Fréquence d'échantillonnage en Hz
Te = 1 / Fe;     % Période d'échantillonnage en secondes
Rb = 3000;       % Débit binaire en bits par seconde
Tb = 1 / Rb;     % Période binaire
Fp = 2000;       % Fréquence porteuse

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%GENERATION D'UNE INFORMATION BINAIRE ALEATOIRE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

bits=randi([0,1],1,Nb_bits);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% MODULATEUR QPSK (8-PSK)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Paramètres du Modulateur
M = 8;                    % Ordre de modulation
n = log2(M);               % Nombre de bits par symbole
Ts = Tb * n;        % Période symbole
Rs = 1/Ts;                % Débit symbole
Ns = Ts/Te;               % Nombre d'échantillons par symbole
Nsb = Nb_bits / n;       % Nombre de symboles
alpha = 0.20;             % Facteur de roll-off
L = 6;                    % Longueur du filtre en durées de symboles

h = rcosdesign(alpha, L, Ns);  % Filtre en cosinus surélevé

%génération des symboles complexes dk
dk = pskmod(reshape(bits, n, Nb_bits/n), M, PlotConstellation=true, InputType='bit');

% Suréchantillonnage des bits
diracs = kron(dk,[1 zeros(1,Ns-1)]);

% Génération de l'enveloppe complexe associée au signal à transmettre
xe = filter(h,1,diracs);

Echelle_Temporelle = 0:Te:(length(xe)-1)*Te; % Echelle temporelle

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% CALCUL DU TEB EN FONCTION DE E_b/N_0
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%génération du filtre de réception adapté
hr = fliplr(h);
% retard induit par le filtrage
retard = (length(h) - 1)/2 + (length(hr) - 1)/2;
% Choix de l'instant d'échantillonnage.
n0=1;

EbN0dB = (0:1:10);                                %choix de Eb/N0
TEBS = zeros(1, length(EbN0dB));                  %tableau des TEB calculés

taille_max_zm = 500;
tab_zm = zeros(length(EbN0dB), taille_max_zm);      %tableau des valeurs des
                                                 %échantillons pour le
                                                 %tracé des constellations

% Pourcentage d'erreur voulu sur la mesure du TEB
epsilon = 0.05;

for i = 1:length(EbN0dB)
    nbr_erreurs = 0;
    N = length(bits);
    while nbr_erreurs < 1/(epsilon^2)       %tant que le nombre d'erreurs
                                            %est trop petit pour
                                            %obtenir epsilon

        xe = filter(h,1,diracs);

        Pxe=mean(abs(xe).^2);

        %Calcul de la puissance du bruit complexe commune aux deux voies
        Pne = Pxe*Ns/(2*log2(M)*10^(EbN0dB(i)/10));

        %Génération du bruit dans chaque voie
        bruit_I = sqrt(Pne)*randn(1,length(xe));
        bruit_Q = sqrt(Pne)*randn(1,length(xe));

        %Ajout du bruit
        xe_bruite = xe + bruit_I + 1i*bruit_Q;

        %Filtrage adapté du signal entrant
        z = filter(hr, 1, xe_bruite);

        %Choix de l'instant d'échantillonnage.
        n0=1;

        % Échantillonnage à n0+mNs en prenant en compte le retard induit
        zm = z(retard+n0:Ns:end);
        tab_zm(i, :) = zm(1:taille_max_zm);

        % Démodulateur
        bm = pskdemod(zm, M, OutputType='bit');
        bm = bm(:)';

        nbr_erreurs = length(find((bm-bits(1:length(bm))) ~=0));
        TEBS(i) = nbr_erreurs/length(bm);

        new_bits = randi([0,1],1,Nb_bits);       %ajout de Nb_bits bits;
        bits = [bits, new_bits];
        N = N + Nb_bits;
        dk = [dk, pskmod(reshape(new_bits, n, Nb_bits/n), M, InputType='bit')];
        diracs = kron(dk,[1 zeros(1,Ns-1)]);
    end


end

% TEB théorique
EbN0 = 10.^(EbN0dB ./ 10);
TEBT = (2/n)*(1-cdf("Normal", sqrt((2*n*10.^(EbN0dB/10)))*sin(pi/M), 0, 1));
TEST = 2 * TEBT;

% Tracé

figure('Name','Comparaison du TEB simulé/théorique')
semilogy(EbN0dB, TEBT, 'r', 'LineWidth', 3)
hold on
semilogy(EbN0dB, TEBS, 'gd', 'LineWidth', 3)
grid
[~, legendIcons] = legend('TEB théorique', 'TEB simulé');
xlabel('Eb/N0 (dB)')
title('Tracé des TEB du signal')
fig2svg("rapport/assets/5_teb.svg", '', '', legendIcons);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%TRACE DES CONSTELLATIONS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
h

%constellation en sortie de l'échantilloneur
for i = 1:5:length(EbN0dB)
    figure
    plot(dk, 'rx', 'Linewidth', 2)
    hold on
    plot(tab_zm(i, :), 'bo')
    grid on
    xlabel('I')
    ylabel('Q')
    title(["Constellation observée en sortie de l'échantillonneur pour E_b/N_0 = ", EbN0dB(i), "dB"] );
    [~, legendIcons] = legend('Constellation en sortie de mapping', "Constellation observée en sortie de l'échantillonneur pour E_b/N_0 = "+ EbN0dB(i)+ "dB");
    fig2svg("rapport/assets/5_constellation_"+num2str(EbN0dB(i))+".svg", '','', legendIcons);
end
