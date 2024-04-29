%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                   TP2 de Télécommunications
%                   SCIENCES DU NUMERIQUE 1A
%                           Avril 2024 
%                        Louis Thevenet
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

clear all
close all

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%PARAMETRES GENERAUX
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
Nb=50;       %nombres de bits générés
Fe=24000;       %fréquence d'échantillonnage en Hz
Te=1/Fe;        %période d'échantillonnage en secondes
Rb=3000;        %débit binaire en bits par secondes
Tb=1/Rb;        %période binaire

% suite de bits
bits = randi([0,1],1,Nb);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% MODULATEUR 1
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

M=2;
Ts_1 = Tb*log2(M);  %période symbole
Rs_1 = 1/Ts_1;      %débit symbole
Ns_1 = Ts_1/Te;
Nsb_1 = Nb/log2(M)

%mapping
ak1 = 2*bits-1;

%surréchantillonage des bits
suite_diracs1 = kron(ak1,[1 zeros(1,Ns_1-1)]);

%mise en place du filtre
B1=ones(1,Ns_1);
x1=filter(B1,1,suite_diracs1);

%Tracé avec une échelle temporelle en secondes
figure
temps1 = [0:Te:(length(x1)-1)*Te];
plot(temps1,x1);
grid
xlabel('Temps (s)')
ylabel('signal')
title('Tracé en temporel du signal 1');


%DSP du signal généré avec le modulateur 1
DSP_1 = pwelch(x1,[],[],[],Fe, 'twosided');

%Echelle fréquentielle 1
echelle_frequentielle_1=linspace(-Fe/2,Fe/2,length(DSP_1));

%tracé du signal
figure
semilogy(echelle_frequentielle_1,fftshift(abs(DSP_1)),'b')
grid
legend('DSP 1')
xlabel('Fréquences (Hz)')
ylabel('DSP')
title('Tracé de la DSP du signal avec le modulateur 1')

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% DEMODULATEUR 1
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Signal demodulé par le filtre de reception (meme que celui de mise en forme)
x1_demodule = filter(B1,1,x1);

%tracé en échelle temporelle
figure 
plot(temps1,x1_demodule)
grid
xlabel('Temps (s)')
ylabel('signal')
title('Tracé en échelle temporelle du signal 1 démodulé');

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% REPONSE IMPULSIONELLE DE LA CHAINE DE TRANSMISSION
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

g = conv(B1,B1);
g_reponse_temporelle = filter(g,1, suite_diracs1);
echelle_temporelle_g = [0:Te:(length(g)-1)*Te];

figure
plot(g_reponse_temporelle);
title('Réponse impulsionelle globale de la chaine de transmission')

G=fft(g);
echelle_frequentielle_g = linspace(-Fe/2,Fe/2,length(G));
figure
semilogy(echelle_frequentielle_g,fftshift(abs(G)),'y')
grid
legend('Réponse impulsionelle globale')
xlabel('Fréquences (Hz)')
ylabel('g')
title('Tracé de la réponse impusionelle globale en fréquence')

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% INSTANT D'ECHANTILLONAGE OPTIMAUX
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%3000 Hz

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% DIAGRAMME DE L'OEIL
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
figure
plot(reshape(x1_demodule,Ns_1,length(x1_demodule)/Ns_1))
%eyediagram( x1_demodule, Ns_1,Ts_1*2);

% Après l'analyse du diagra&mme de l'oeil, on constate qu'il faut prendre
% n0=8 car c'est l'endroit où les droites s'y croisent. 

%Il faut dont démoduler le signal avec un décalage de n0 = 8
x1_demodule_decalage = x1_demodule(8:Ns_1:end);

%tracé en échelle temporelle
temps_decalage = [0:Te:(length(x1_demodule)-1)*Te];
figure 
plot(temps_decalage,x1_demodule)
grid
xlabel('Temps (s)')
ylabel('signal')
title('Tracé en échelle temporelle du signal 1 démodulé de façon optimale');


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TAUX D'ERREUR BINAIRE (TEB)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%TEB= nb_bits_erreur/nb_bits

K = 0;

bits_sortis = x1_demodule_decalage > K;
nb_bits_erreur = sum(bits_sortis ~= bits);

TEB = nb_bits_erreur/Nb;
TEB

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TAUX D'ERREUR BINAIRE BIAISE (TEBB)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

x1_demodule_decalage_biaise = x1_demodule(3:Ns_1:end);

bits_sortis_biaise = x1_demodule_decalage_biaise > K;
nb_bits_erreur_biaise = sum(bits_sortis_biaise ~= bits);

TEBB = nb_bits_erreur_biaise/Nb;
TEBB

% Si l'échantillonage n'est pas optimal, alors le taux d'erreur bianaire
% est non nul