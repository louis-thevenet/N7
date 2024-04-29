%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                   TP1 de Télécommunications
%                   SCIENCES DU NUMERIQUE 1A
%                           Avril 2024 
%                         Louis Thevenet
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

clear all
close all

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%PARAMETRES GENERAUX
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
Nb=200;         %nombres de bits générés
Fe=24000;       %fréquence d'échantillonnage en Hz
Te=1/Fe;        %période d'échantillonnage en secondes
Rb=3000;        %débit binaire en bits par secondes
Tb=1/Rb;        %période binaire

% suite de bits à transmettre
bits = randi([0,1],1,Nb); % renvoie un vecteur de taille 1xNb avec des valeurs suivant une loin uniforme entre O et 1


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%MODULATEUR 1
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

M=2;
Ts_1 = Tb*log2(M);  %période symbole
Rs_1 = 1/Ts_1;      %débit symbole
Ns_1 = Ts_1/Te;
Nsb_1 = Nb/log2(M);

%mapping
ak1 = 2*bits-1;

%surréchantillonage des bits
suite_diracs1 = kron(ak1,[1 zeros(1,Ns_1-1)]);

%mise en place du filtre
B1=ones(1,Ns_1);
x1=filter(B1,1,suite_diracs1);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%TRACE DU SIGNAL 1
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Tracé avec une échelle temporelle en secondes
figure
temps1 = 0:Te:(length(x1)-1)*Te;
plot(temps1,x1);
grid
xlabel('Temps (s)')
ylabel('signal')
title('Tracé en temporel du signal 1 en sortie de filtre de mise en forme');

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%TRACE DE LA DENSITE SPECTRALE DE PUISSANCE (DSP) DU SIGNAL 1
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Transformée de fourier
%X1=fft(x1, 512);
%echelle_frequentielle=linspace(-Fe/2,Fe/2,length(X1));
%figure
%semilogy(echelle_frequentielle,fftshift(abs(X1).^2/length(X1)),'b')
%grid
%legend('DSP 1')
%xlabel('Fréquences (Hz)')
%ylabel('DSP')
%title('Tracés de la DSP du signal 1');


%DSP du signal généré avec le modulateur 1
DSP_1 = pwelch(x1,[],[],[],Fe, 'twosided');

%Echelle fréquentielle 1
echelle_frequentielle_1=linspace(-Fe/2,Fe/2,length(DSP_1));

%tracé du signal
figure
semilogy(echelle_frequentielle_1,fftshift(abs(DSP_1)),'b')  % fftshift pour centrer en 0 // semilogy pour avoir une échelle logarithmique des y
grid
legend('DSP 1')
xlabel('Fréquences (Hz)')
ylabel('DSP')
title('Tracé de la DSP du signal avec le modulateur 1 en sortie de filtre de mise en forme')
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%MODULATEUR 2
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
M=4;
Ts_2 = Tb*log2(M);  %période symbole
Rs_2 = 1/Ts_2;      %débit symbole
Ns_2 = Ts_2/Te;
Nsb_2 = Nb/log2(M);

%mapping
entiers = bi2de(reshape(bits,2,Nb/2)');
ak2 = pammod(entiers,M);

%for i=1:length(bits)/log2(M)
%    if bits(i)==0 && bits(i+1)==0
%       ak2(i) = -3;
%    elseif bits(i)==1 && bits(i+1)==0
%        ak2(i) = -1;
%    elseif bits(i)==0 && bits(i+1)==1
%        ak2(i) = 1;
%    else
%        ak2(i) = 3;
%    end
%end

%surréchantillonage des bits
suite_diracs2 = kron(ak2',[1 zeros(1,Ns_2-1)]);

%mise en place du filtre
B=ones(1,Ns_2);
x2=filter(B,1,suite_diracs2);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%TRACE DU SIGNAL 2
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Tracé avec une échelle temporelle en secondes
figure
temps2 = 0:Te:(length(x2)-1)*Te;
plot(temps2,x2);
grid
xlabel('Temps (s)')
ylabel('signal')
title('Tracé avec une échelle temporelle du signal 2 en sortie du filtre de mise en forme');

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%TRACE DE LA DENSITE SPECTRALE DE PUISSANCE (DSP) DU SIGNAL 2
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Transformée de fourier
%X2=fft(x2, 512);

%figure
%echelle_frequentielle=linspace(-Fe/2,Fe/2,length(X2));
%semilogy(echelle_frequentielle,fftshift(abs(X2).^2/length(X2)),'r')
%grid
%legend('DSP 2')
%xlabel('Fréquences (Hz)')
%ylabel('DSP')
%title('Tracés de la DSP du signal 2');

%DSP du signal généré avec le modulateur 1
DSP_2 = pwelch(x2,[],[],[],Fe, 'twosided');

%Echelle fréquentielle 1
echelle_frequentielle_2=linspace(-Fe/2,Fe/2,length(DSP_2));

%tracé du signal
figure
semilogy(echelle_frequentielle_2,fftshift(abs(DSP_2)),'r')
grid
legend('DSP 2')
xlabel('Fréquences (Hz)')
ylabel('DSP')
title('Tracé de la DSP du signal avec le modulateur 2')

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%MODULATEUR 3
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
M=2;
Ts_3 = Tb*log2(M);  %période symbole
Rs_3 = 1/Ts_3;      %débit symbole
Ns_3 = Ts_3/Te;
Nsb_3 = Nb/log2(M);

alpha = 0.5;
L = 50;
h = rcosdesign(alpha,L,Ns_3);

% même mapping que pour le premier modulateur

%mise en place du filtre
x3=filter(h,1,suite_diracs1);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%TRACE DU SIGNAL 3
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Tracé avec une échelle temporelle en secondes
figure
temps2 = 0:Te:(length(x3)-1)*Te;
plot(temps2,x3);
grid
xlabel('Temps (s)')
ylabel('signal')
title('Tracé avec une échelle temporelle du signal 3 en sortie de filtre de mise en forme');

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%TRACE DE LA DENSITE SPECTRALE DE PUISSANCE (DSP) DU SIGNAL 3
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%DSP du signal généré avec le modulateur 3
DSP_3 = pwelch(x3,[],[],[],Fe, 'twosided');

%Echelle fréquentielle 3
echelle_frequentielle_3=linspace(-Fe/2,Fe/2,length(DSP_3));

%tracé du signal
figure
semilogy(echelle_frequentielle_3,fftshift(abs(DSP_3)),'g')
grid
legend('DSP 3')
xlabel('Fréquences (Hz)')
ylabel('DSP')
title('Tracé de la DSP du signal avec le modulateur 3')

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%COMPARAISON DES 3 DSP
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
figure
semilogy(echelle_frequentielle_1,fftshift(abs(DSP_1)),'b')   
hold on
semilogy(echelle_frequentielle_2,fftshift(abs(DSP_2)),'r')
hold on
semilogy(echelle_frequentielle_3,fftshift(abs(DSP_3)),'g')
grid
legend('Modulateur 1','Modulateur 2', 'Modulateur 3')
xlabel('Fréquence (Hz)')
ylabel('DSP')
title('Superposition des 3 DSP des signaux filtrés')

 
 
