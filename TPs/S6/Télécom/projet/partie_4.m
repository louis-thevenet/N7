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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%GENERATION D'UNE INFORMATION BINAIRE ALEATOIRE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

bits=randi([0,1],1,Nb_bits);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% MODULATEUR 4-ASK
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Paramètres du Modulateur
M = 4;                    % Ordre de modulation
n = log2(M);               % Nombre de bits par symbole
Ts = Tb * n;        % Période symbole
Rs = 1/Ts;                % Débit symbole
Ns = Ts/Te;               % Nombre d'échantillons par symbole
Nsb = Nb_bits / n;       % Nombre de symboles
alpha = 0.35;             % Facteur de roll-off
L = 12;                    % Longueur du filtre en durées de symboles

h = rcosdesign(alpha, L, Ns);  % Filtre en cosinus surélevé

% Mapping 4-ASK (de Gray)
mapping = [-3, -1, 3, 1];

%génération des symboles complexes dk
dk = mapping(bin2dec(int2str([bits(1:2:Nb_bits-1)', bits(2:2:Nb_bits)']))+1);

% Suréchantillonnage des bits
diracs = kron(dk,[1 zeros(1,Ns-1)]);

% Génération de l'enveloppe complexe associée au signal à transmettre
xe = filter(h,1,diracs);

Echelle_Temporelle = 0:Te:(length(xe)-1)*Te; % Echelle temporelle

% Constellation en sortie du mapping
%constellation en sortie du mapping
figure
plot(dk, zeros(1, length(dk)), 'rx')
grid on
xlabel('I')
ylabel('Q')
title("Constellation observée en sortie du mapping");
[~, legendIcons] = legend("Constellation observée en sortie du mapping");
fig2svg("rapport/assets/4_constellation.svg", '','', legendIcons);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% DSP (Densité Spectrale de Puissance)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Calcul de la DSP de l'enveloppe complexe associée au signal à transmettre
[S_xe] = pwelch(xe, [], [], [], Fe, 'twosided');
S_xe_log = 10*log(S_xe/max(S_xe));

% Échelle de fréquence
taille_S_xe = length(S_xe);
Echelle_Frequentielle= (-taille_S_xe/2:taille_S_xe/2-1)*Fe/taille_S_xe;

% Tracé de la DSP en dB de l'enveloppe complexe associée au signal à
% Transmettre en utilisant 4-ASK
figure
plot(Echelle_Frequentielle, fftshift(S_xe_log), 'r')
hold on

% Tracé de la DSP en dB de l'enveloppe complexe associée au signal à
% Transmettre en utilisant QPSK
load('S_xe_partie_3.mat')
S_xe_log = 10*log(S_xe/max(S_xe));
plot(Echelle_Frequentielle, fftshift(S_xe_log), 'b')

%Tracé du seuil -x dB
x_dB = 20; %atténuation seuil bande
yline(-x_dB,'k', LineWidth=1, LineStyle='-.');

grid("on");
xlabel('f (Hz)')
ylabel('S_x (dB)')
title("Tracé de la DSP de l'enveloppe complexe associée au signal à transmettre");
[~, legendIcons] = legend('4-ASK', 'QPSK');
fig2svg("rapport/assets/4_2_dsp_comparaison.svg", '','', legendIcons);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% CALCUL DU TEB EN FONCTION DE E_b/N_0
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Génération du filtre de réception adapté
hr = fliplr(h);
% Retard induit par le filtrage
retard = (length(h) - 1)/2 + (length(hr) - 1)/2;
% Choix de l'instant d'échantillonnage.
n0=1;

EbN0dB = (0:0.2:6);                                %choix de Eb/N0
TEBS = zeros(1, length(EbN0dB));                  %tableau des TEB calculés

taille_max_zm = 200;
tab_zm = zeros(length(EbN0dB), taille_max_zm);      %tableau des valeurs des
                                                 %échantillons pour le
                                                 %tracé des constellations

% Pourcentage d'erreur voulu sur la mesure du TEB
epsilon = 0.05;

for i = 1:length(EbN0dB)
    nbr_erreurs = 0;
    N = length(bits);
    while nbr_erreurs < 1/(epsilon^2)

        xe = filter(h,1,diracs);

        Pxe = mean(abs(xe).^2);

        % Calcul de la puissance du bruit
        Pne = Pxe*Ns/(2*n*10^(EbN0dB(i)/10));

        % Génération du bruit
        bruit = sqrt(Pne)*randn(1,length(xe));

        % Ajout du bruit
        xe_bruite = xe + bruit;

        % Filtrage adapté du signal entrant
        z = filter(hr, 1, xe_bruite);


        % Choix de l'instant d'échantillonnage.
        n0=1;

        % Échantillonnage à n0+mNs en prenant en compte le retard induit
        zm = z(retard+n0:Ns:end);
        tab_zm(i, :) = zm(1:taille_max_zm);

        %Décision sur les symboles
        portion_seuil = 2;
        am = 3 * (zm > portion_seuil) - 3 * (-zm > portion_seuil) ...
           + (zm > 0 & zm < portion_seuil) ...
           - (zm < 0 & -zm < portion_seuil);


        % Demapping
        bm = dec2bin((am==-1) + 3*(am==1) + 2*(am==3), 2)';
        bm = str2num(bm(:))';
        % Calcul du TEB
        nbr_erreurs = length(find((bm-bits(1:length(bm))) ~=0));
        TEBS(i) = nbr_erreurs/length(bm);

        new_bits = randi([0,1],1,Nb_bits);       %ajout de Nb_bits bits;
        bits = [bits, new_bits];
        N = N + Nb_bits;

        dk = [dk, mapping(bin2dec(int2str([new_bits(1:2:(Nb_bits-1))', new_bits(2:2:Nb_bits)'])) + 1)];
        diracs = kron(dk,[1 zeros(1,Ns-1)]);
    end


end

% TEB théorique
EbN0 = 10.^(EbN0dB ./ 10);
TEBT =  (2*(M-1)/(n*M))*(1-cdf("Normal", sqrt((6*n/(M^2-1))*(10.^(EbN0dB/10))), 0, 1));
TEST = 2 * TEBT;

% Tracé

figure('Name','Comparaison du TEB simulé/théorique')
semilogy(EbN0dB, TEBT, 'r', 'LineWidth', 3)
hold on
semilogy(EbN0dB, TEBS, 'gd', 'LineWidth', 3)
grid
[~, legendIcons] = legend('TEB théorique', 'TEB simulé');
xlabel('Eb/N0 (dB)')
title('Tracé du TEB - 4-ASK')
fig2svg("rapport/assets/4_teb.svg", '', '', legendIcons);


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%COMPARAISON DE L'EFFICACITE EN PUISSANCE DE QPSK ET DE 4-ASK
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Tracé du TEB obtenu avec 4-ASK
figure
semilogy(EbN0dB, TEBS, "gd");
hold on

% Tracé du TEB obtenu avec QPSK
load('TEB_partie_3');
semilogy(EbN0dB, TEBS);
[~, legendIcons] = legend('TEB avec 4-ASK', 'TEB avec QPSK');
xlabel('E_b/N_0 (dB)')
ylabel('TEB')
grid on
title("Graphe du TEB en fonction de E_b/N_0");
fig2svg("rapport/assets/4_comparaison_eff_puiss.svg", '','', legendIcons);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%TRACE DES CONSTELLATIONS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Constellation en sortie de l'échantilloneur
for i = 1:5:length(EbN0dB)
    figure
    plot([-3, -1, 1, 3], zeros(1, 4), 'rx', 'LineWidth', 2)
    hold on
    plot(tab_zm(i, :), zeros(1, length(tab_zm(i, :))), 'bo')
    grid on
    xlabel('I')
    ylabel('Q')
    title(["Constellation observée en sortie de l'échantillonneur pour E_b/N_0 = ", EbN0dB(i), "dB"]);
    [~, legendIcons] = legend('Constellation en sortie de mapping', "Constellation observée en sortie de l'échantillonneur pour E_b/N_0 = "+ EbN0dB(i)+ "dB");
    fig2svg("rapport/assets/4_constellation_"+num2str(EbN0dB(i))+".svg", '','', legendIcons);
end
