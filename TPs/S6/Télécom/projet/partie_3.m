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
%% GENERATION D'UNE INFORMATION BINAIRE ALEATOIRE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

bits = randi([0, 1], 1, Nb_bits);

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

% Tracé des signaux générés sur les voies en phase et en quadrature
figure('Name','Signaux Générés/Transmis - Bande de Base');
subplot(2,1,1)
plot(Echelle_Temporelle, I);
xlabel('t (s)')
ylabel('I(t) ')
title('Tracé du signal généré en phase');
subplot(2,1,2)
plot(Echelle_Temporelle, Q)
xlabel('t (s)')
ylabel('Q(t)')
title('Tracé du signal généré sur la voie en quadrature');
[~, legendIcons] = legend('Signal généré sur la voie en phase', 'Signal généré sur la voie en quadrature');
fig2svg("rapport/assets/3_signal.svg", '','', legendIcons);

% Constellation en sortie du mapping
figure
plot(dk, 'rx', 'LineWidth', 2)
grid on
xlabel('I')
ylabel('Q')
title("Constellation observée en sortie du mapping");
[~, legendIcons] = legend("Constellation des symboles modulés");
fig2svg("rapport/assets/3_constellation.svg", '','', legendIcons);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% DSP (Densité Spectrale de Puissance)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Calcul de la DSP de l'enveloppe complexe associée au signal à transmettre
[S_xe] = pwelch(xe, [], [], [], Fe, 'twosided');

% Sauvegarde de la DSP pour la comparaison avec celle pour 4-ASK
save('S_xe_partie_3', 'S_xe');

% Échelle de fréquence
taille_S_xe = length(S_xe);
Echelle_Frequentielle = (-taille_S_xe/2:taille_S_xe/2-1)*Fe/taille_S_xe;

% Tracé de la DSP de l'enveloppe complexe associée au signal à transmettre
figure
semilogy(Echelle_Frequentielle, fftshift(S_xe))
grid on
xlabel('f (Hz)')
ylabel('S_xe(f)')
xline((1+alpha)/(Ts*2),'k', LineWidth=0.7, LineStyle='-.')
text((1+alpha)/(Ts*2), 10^(-8), '(1+\alpha)*R_s/2')
title("Tracé de la DSP de l'enveloppe complexe associée au signal à transmettre");
[~, legendIcons] = legend("DSP de l\'enveloppe complexe - Bande de Base");
fig2svg("rapport/assets/3_dsp.svg", '','', legendIcons);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% CALCUL DU TEB EN FONCTION DE E_b/N_0
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Calcul et tracé du TEB
% Comparaison du TEB simulé avec le TEB théorique
%3.5

% Génération du filtre de réception adapté
hr = fliplr(h);

% Prise en compte du retard introduit par le filtrage
retard = (length(h) - 1)/2 + (length(hr) - 1)/2;

% Choix de l'instant d'échantillonnage.
n0=1;

EbN0dB = (0:0.2:6);                                %choix de Eb/N0
TEBS = zeros(1, length(EbN0dB));                  %tableau des TEB calculés

taille_max_zm = 200;
tab_zm = zeros(length(EbN0dB), taille_max_zm);   %tableau des valeurs des
                                                 %échantillons pour le
                                                 %tracé des constellations

% Pourcentage d'erreur voulu sur la mesure du TEB
epsilon = 0.15;

for i = 1:length(EbN0dB)
    nbr_erreurs = 0;
    N = length(bits);
    while nbr_erreurs < 1/(epsilon^2)

        xe = filter(h,1,diracs);

        Pxe=mean(abs(xe).^2);

        % Calcul de la puissance du bruit complexe commune aux deux voies
        Pne = Pxe*Ns/(2*log2(M)*10^(EbN0dB(i)/10));

        % Génération du bruit dans chaque voie
        bruit_I = sqrt(Pne)*randn(1,length(xe));
        bruit_Q = sqrt(Pne)*randn(1,length(xe));

        % Ajout du bruit
        xe_bruite = xe + bruit_I + 1i*bruit_Q;

        % Filtrage adapté du signal entrant
        z = filter(hr, 1, xe_bruite);

        % Choix de l'instant d'échantillonnage.
        n0=1;

        % Échantillonnage à n0+mNs en prenant en compte le retard induit
        zm = z(retard+n0:Ns:end);
        tab_zm(i, :) = zm(1:taille_max_zm);

        % Décisions sur les symboles
        am1 = sign(real(zm));
        am2 = sign(imag(zm));

        % Demapping
        bm=[(am1+1)/2; (am2+1)/2];
        bm = bm(:)';

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
%3.6
EbN0 = 10.^(EbN0dB ./ 10);
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

% Sauvegarde du tableau des TEB pour la comparaison avec la partie 4
save('TEB_partie_3', 'TEBS');

%Tracé du TEB obtenu dans la partie 2
figure('Name','Comparaison du TEB DVBS2 et TEB QPSK')
semilogy(EbN0dB, TEBS, 'gd', 'LineWidth', 3)
hold on
load('TEB_partie_2');
semilogy(EbN0dB, TEBS,'b', 'LineWidth', 3);
  [~, legendIcons] =legend('TEB avec le passe-bas équivalente', 'TEB avec la transposition de fréquence');
xlabel('E_b/N_0 (dB)')
ylabel('TEB')
title("Graphe du TEB en fonction de E_b/N_0");
fig2svg("rapport/assets/3_teb.svg", '','', legendIcons);
grid on;

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%COMPARAISON TEB PRECEDENT
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Tracé du TEB obtenu avec 4-ASK
figure
semilogy(EbN0dB, TEBS, "gd");
hold on

% Tracé du TEB obtenu avec QPSK
load('TEB_partie_2');
semilogy(EbN0dB, TEBS);
[~, legendIcons] = legend('TEB avec QPSK', 'TEB avec chaine passe-bas équivalente');
xlabel('E_b/N_0 (dB)')
ylabel('TEB')
grid on
title("Graphe du TEB en fonction de E_b/N_0");
fig2svg("rapport/assets/3_comparaison_eff_puiss.svg", '','', legendIcons);


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%TRACE DES CONSTELLATIONS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Constellation en sortie de l'échantilloneur
for i = 1:5:length(EbN0dB)
  figure
  plot(dk, 'rx', 'LineWidth', 2)
  hold on
  plot(tab_zm(i, :), 'bo')
  grid on
  xlabel('I')
  ylabel('Q')
  title(["Constellation observée en sortie de l'échantilloneur pour E_b/N_0 = ", EbN0dB(i), "dB"] );
    [~, legendIcons] = legend("Constellation en sortie de mapping",['Constellation des symboles reçus - Eb/N0 = ' num2str(EbN0dB(i)) ' dB']);
    fig2svg("rapport/assets/3_constellation_"+num2str(EbN0dB(i))+".svg", '','', legendIcons);
    grid on;
end