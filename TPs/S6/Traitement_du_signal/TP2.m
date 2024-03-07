%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%               TP1 de Traitement Numérique du Signal
%                   SCIENCES DU NUMERIQUE 1A
%                       Fevrier 2024 
%                        Louis THEVENET
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

clear all
close all

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%PARAMETRES GENERAUX
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
A=1;        %amplitude du cosinus
f1=1000;       %fréquence du cosinus  en Hz
f2=3000;

N=100;        %nombre d'échantillons souhaités pour le cosinus
Fe=10000;       %fréquence d'échantillonnage en Hz
Te=1/Fe;       %période d'échantillonnage en secondes
SNR="à completer";      %SNR souhaité en dB pour le cosinus bruité

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%GENERATION DU COSINUS NUMERIQUE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Définition de l'échelle temporelle
temps=[0:N-1] * Te;
x=A*cos(2*pi*f1*temps) + A*cos(2*pi*f2*temps);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%TRACE DU COSINUS NUMERIQUE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%Tracé avec une échelle temporelle en secondes
%des labels sur les axes et un titre (utilisation de xlabel, ylabel et
%title)
figure
plot(temps, x);
grid
xlabel('Temps (s)')
ylabel('signal')
title(['Tracé d''une somme de cosinus numérique']);



% TRANSFORMEE DE FOURIER

X=fft(x);



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%TRACE DU MODULE DE LA TFD DU COSINUS NUMERIQUE EN ECHELLE LOG
%SANS PUIS AVEC ZERO PADDING
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Avec une échelle fréquentielle en Hz
%des labels sur les axes et des titres
%Tracés en utilisant pl2 6usieurs zones de la figure (utilisation de subplot) 
figure('name',['Tracé du module de la TFD de la somme de cosinus'])

echelle_frequentielle=linspace(0, Fe, length(X));
semilogy(echelle_frequentielle, abs(fftshift(X)));
grid
title('Sans zero padding')
xlabel('Fréquence (Hz)')
ylabel('|TFD|')


ordre = 11;
Fc = 2*f1;
h = 2 * Fc / Fe * sinc(2*Fc * [-(ordre - 1)/2 + Te :Te:(ordre-1)*Te/2 ]);
y = filter(h, 1,x);
Y=fft(y);

ordre = 61;
Fc = 2*f1;
h2 = 2 * Fc / Fe * sinc(2*Fc * [-(ordre - 1)/2 + Te :Te:(ordre-1)*Te/2 ]);
y2 = filter(h2, 1,x);
Y2 = fft(y2);
%Avec une échelle fréquentielle en Hz
%des labels sur les axes et des titres
%Tracés en utilisant pl2 6usieurs zones de la figure (utilisation de subplot) 
figure('name',['Tracé de la Sortie'])
echelle_frequentielle=linspace(0, Fe, length(Y));
semilogy(echelle_frequentielle, abs(fftshift(Y)), 'g');
hold on
echelle_frequentielle=linspace(0, Fe, length(Y2));

semilogy(echelle_frequentielle, abs(fftshift(Y2)), 'b');

grid
title('Sortie')
xlabel('Fréquence (Hz)')
ylabel('|Y|')




