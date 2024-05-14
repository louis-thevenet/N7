clear all
close all
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                   PROJET TÉLÉCOM/SIGNAL                                        %
%      Étude dÉune chaine de transmission sur porteuse pour une transmission satellite fixe      %
%                   THEVENET Louis & LÉCUYER Simon 1A SN ENSEEIHT 2023/2024                      %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% PARAMETRES GENERAUX
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
Nb=2000;       %nombres de bits générés
Fe=24000;       %fréquence d'échantillonnage en Hz
Te=1/Fe;        %période d'échantillonnage en secondes
Rb=3000;        %débit binaire en bits par secondes
Tb=1/Rb;        %période binaire
Fp = 2000;      %fréquence porteuse

% Suite de bits / Information à transmettre 
bits = randi([0,1],1,Nb);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% MODULATEUR QPSK
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Paramètres du Modulateur 
M = 4;
Ts = Tb*log2(M);  %période symbole
Rs = 1/Ts;      %débit symbole
Ns = Ts/Te;
Nsb = Nb/log2(M);
alpha = 0.35; %roll-off factor
L = 6;
h = rcosdesign(alpha,L,Ns);

%Mapping QPSK

dk = 1-2*bits(1:2:Nb)+1i*(1-2*bits(2:2:Nb));

%Surréchantillonage des bits

suite_diracs_ak = kron(real(dk),[1 zeros(1,Ns-1)]);
suite_diracs_bk = kron(imag(dk),[1 zeros(1,Ns-1)]);

%Filtrage

I = filter(h, 1,suite_diracs_ak );
Q = filter(h, 1,suite_diracs_bk );
temps_phase = 0:Te:(length(I)-1)*Te;

x = real(( I + Q*1i) .* exp(2*pi*1i*Fp*temps_phase));


Echelle_Temporelle= 0:Te:(length(x)-1)*Te;

% Tracés des Signaux Générés/Transmis
figure('Name','Signaux Générés/Transmis')
 
%2.1
subplot(3,1,1)
plot(Echelle_Temporelle,I)
xlabel("temps (s)")
ylabel("I(t)")
title("Signal généré sur la voie en phase")


subplot(3,1,2)
plot(Echelle_Temporelle,Q)
xlabel("temps (s)")
ylabel("Q(t)")
title("Signal généré sur la voie en quadrature")

%2.2
subplot(3,1,3)
plot(Echelle_Temporelle,x)
xlabel("temps (s)")
ylabel("x(t)")
title("Signal transmis sur fréquence porteuse")

    

% Calcul et Tracé de la DSP
%2.3
X=fft(x, 512);
echelle_frequentielle=linspace(-Fe/2,Fe/2,length(X));
figure('Name','DSP')
semilogy(echelle_frequentielle,fftshift(abs(X).^2/length(X)),'b')
grid
legend('DSP')
xlabel('Fréquences (Hz)')
ylabel('DSP')
title('Tracés de la DSP du signal transmis sur fréquence porteuse');

%2.4
%TODO : EXPLICATION DE LA DSP

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% INTRODUCTION DU BRUIT
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 
SNR = 10; %(Eb/N0)

Px = mean(abs(x).^2);
sigma2 = (Px*Ns)./(2*log2(M)*SNR);
bruit = sqrt(sigma2)*randn(1,length(x));

r=x+bruit; %signal bruité

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% DEMODULATEUR 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Signal auquelle on enlève la fréquence porteuse
y=r.*cos(2*pi*Fp*Echelle_Temporelle)-1i*r.*sin(2*pi*Fp*Echelle_Temporelle);

%Signal demodulé par le filtre de reception (meme que celui de mise en forme)
z = filter(h,1,y);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Diagramme de l'oeil/Determination de N0
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

eyediagram(z,2*Ns,2*Ns)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% TEB SIMULÉ/THÉORIQUE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Calcul et Tracé du TEB
%2.5 :Comparaison du TEB simulé avec le TEB théorique

%TEB simulé

%décalage avec l'instant optimal
z_decalage = z(length(h):Ns:end);

%seuil optimal de décision
K = 0;

%détection de seuil
xr = zeros(1,Nb);
xr(1:2:Nb-2*L) = (real(z_decalage) <0);
xr(2:2:Nb-2*L) = (imag(z_decalage) <0);


%Taux d'erreur binaire

TEB = mean(xr ~= bits)

SNRmax=6;

TEBS=zeros(SNRmax,1);

for SNR=1:1:SNRmax
    sigma2 = (Px*Ns)./(2*log2(M)*SNR);
    bruit = sqrt(sigma2)*randn(1,length(x));

    r=x+bruit; %signal bruité
    
    %Signal auquelle on enlève la fréquence porteuse
    y=r.*cos(2*pi*Fp*Echelle_Temporelle)-1i*r.*sin(2*pi*Fp*Echelle_Temporelle);

    %Signal demodulé par le filtre de reception (meme que celui de mise en forme)
    z = filter(h,1,y);

    %décalage avec l'instant optimal
    z_decalage = z(length(h):Ns:end);
    
    %seuil optimal de décision
    K = 0;
    
    %détection de seuil
    xr = zeros(1,Nb);
    xr(1:2:Nb-2*L) = (real(z_decalage) <0);
    xr(2:2:Nb-2*L) = (imag(z_decalage) <0);

    TEBS(SNR)=mean(xr ~= bits);
end




%TEB théorique


%TEB = Q(sqrt(2*Eb/N0))
SNR = 1:1:SNRmax;
Eb_n0=10.^(SNR/10);
TEBT = qfunc(sqrt(4/5*Eb_n0));

%Tracé
figure('Name','Comparaison du TEB simulé/théorique')
semilogy(SNR,TEBT,'b')
hold on
semilogy(SNR,TEBS,'r')
grid
legend('TEB théorique', 'TEB simulé')
xlabel('Eb/N0')
title('Tracé des TEB du signal avec le modulateur 3')

