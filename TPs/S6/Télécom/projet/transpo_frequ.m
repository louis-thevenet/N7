clear all
close all

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%PARAMETRES GENERAUX
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
Nb=2000;       %nombres de bits générés
Fe=24000;       %fréquence d'échantillonnage en Hz
Te=1/Fe;        %période d'échantillonnage en secondes
Rb=3000;        %débit binaire en bits par secondes
Tb=1/Rb;        %période binaire
Fp = 2000;      %fréquence porteuse

% suite de bits
bits = randi([0,1],1,Nb);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%MODULATEUR
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Mapping
M = 4;
Ts = Tb*log2(M);  %période symbole
Rs = 1/Ts;      %débit symbole
Ns = Ts/Te;
Nsb = Nb/log2(M);

%mapping

dk = zeros(1, Nb/2);
for k=1:Nb/log2(M)
   if bits(2*k-1)==0 && bits(2*k)==0
      dk(k) = -1-1i;
   elseif bits(2*k-1)==1 && bits(2*k)==0
       dk(k) = 1-1i;
   elseif bits(2*k-1)==0 && bits(2*k)==1
       dk(k) = -1+1i;
   else
       dk(k) = 1+1i;
   end
end


%surréchantillonage des bits

suite_diracs_ak = kron(real(dk),[1 zeros(1,Ns-1)]);
suite_diracs_bk = kron(imag(dk),[1 zeros(1,Ns-1)]);

% Filter
alpha = 0.35;
L = 3;
h = rcosdesign(alpha,L,Ns);

I = filter(h, 1,suite_diracs_ak );
Q = filter(h, 1,suite_diracs_bk );
temps_phase = [0:Te:(length(I)-1)*Te];

x =real(( I + Q*1i) .* exp(2*pi*1i*Fp*temps_phase));


T= [0:Te:(length(x)-1)*Te];

% Tracés
figure('name', 'Modulateur')

    % Signal généré
subplot(3,1,1)
    plot(T,I)
    xlabel("temps (s)")
    ylabel("I(t)")
    
    subplot(3,1,2)
    plot(T,Q)
    xlabel("temps (s)")
    ylabel("Q(t)")

    subplot(3,1,3)
    plot(T,x)
    xlabel("temps (s)")
    ylabel("x(t)")
    title("Signal transmis sur fréquence porteuse")

    

% Transformée de fourier
X=fft(x, 512);
echelle_frequentielle=linspace(-Fe/2,Fe/2,length(X));
figure
semilogy(echelle_frequentielle,fftshift(abs(X).^2/length(X)),'b')
grid
legend('DSP')
xlabel('Fréquences (Hz)')
ylabel('DSP')
title('Tracés de la DSP du signal transmis sur fréquence porteuse');



