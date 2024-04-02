Fe = 24000;
Te = 1/Fe;

Rb = 3000;
Tb = 1/Rb;

bits = [0 1 1 0 1 0 0 1 0 0 1 1];



%%%%%%%%%%%%%%%%
% Modulateur 1 %
%%%%%%%%%%%%%%%%
M = 2;
Ts = log2(M)*Tb;
Ns = Ts/Te;
ak = 2* bits - 1;
suite_dirac = kron(ak, [1 zeros(1,Ns-1)]);
y_1 = filter(ones(1, Ns), 1, suite_dirac);

temps=(0:length(suite_dirac)-1) * Ts;

figure
subplot(4,1,1)
plot(temps, y_1);
grid
xlabel('Temps (s)')
ylabel('signal')
title('Tracé de la sortie du filtre modulateur 1');

%%%%%%%%%%%%%%%%
% Modulateur 2 %
%%%%%%%%%%%%%%%%
M = 4;
Ts = log2(M)*Tb;
Ns = Ts/Te;
ak = zeros(1, length(bits));


for i=1:length(bits)/log2(M)
    if bits(i)==0
        if bits(i+1)==0
            ak(i) = -3;
        else
            ak(i)=-1;
        end
    else
        if bits(i+1)==0
            ak(i) = 1;
        else
            ak(i)=3;
        end
    end
end

suite_dirac = kron(ak, [1 zeros(1,Ns-1)]);
y_2 = filter(ones(1, Ns), 1, suite_dirac);

temps=(0:length(suite_dirac)-1) * Ts;

subplot(4,1,2)
plot(temps, y_2);
grid
xlabel('Temps (s)')
ylabel('signal')
title('Tracé de la sortie du filtre modulateur 2');

%%%%%%%%%%%%%%%%
% Modulateur 3 %
%%%%%%%%%%%%%%%%
M = 2;
Ts = log2(M)*Tb;
Ns = Ts/Te;
ak = 2* bits - 1;
suite_dirac = kron(ak, [1 zeros(1,Ns-1)]);
h = rcosdesign(0.5, length(suite_dirac)*Ns+1, Ns);
y_3 = filter(h, 1, suite_dirac);

temps=(0:length(suite_dirac)-1) * Ts;


subplot(4,1,3)
plot(temps, y_3);
grid
xlabel('Temps (s)')
ylabel('signal')
title('Tracé de la sortie du filtre modulateur 3');



%%%%%%%%%%%%%%%%
% Modulateur 1 %
%%%%%%%%%%%%%%%%
Y_1=fft(y_1, pow2(16));
Sx_periodogramme=abs(Y_1).*abs(Y_1)/length(y_1);

figure
subplot(4,1,1)
echelle_frequentielle=linspace(0, Fe, length(Sx_periodogramme));
semilogy(echelle_frequentielle, fftshift(Sx_periodogramme));
grid
title('Densité spectrale modulateur 1')
xlabel('Fréquence (Hz)')
ylabel('TFD')

%%%%%%%%%%%%%%%%
% Modulateur 2 %
%%%%%%%%%%%%%%%%
Y_2=fft(y_2, pow2(16));
Sx_periodogramme=abs(Y_2).*abs(Y_2)/length(y_2);


subplot(4,1,2)
echelle_frequentielle=linspace(0, Fe, length(Sx_periodogramme));
semilogy(echelle_frequentielle, fftshift(Sx_periodogramme));
grid
title('Densité spectrale modulateur 2')
xlabel('Fréquence (Hz)')
ylabel('TFD')

%%%%%%%%%%%%%%%%
% Modulateur 3 %
%%%%%%%%%%%%%%%%
Y_3=fft(y_3, pow2(16));
Sx_periodogramme=abs(Y_3).*abs(Y_3)/length(y_3);


subplot(4,1,3)
echelle_frequentielle=linspace(0, Fe, length(Sx_periodogramme));
semilogy(echelle_frequentielle, fftshift(Sx_periodogramme));
grid
title('Densité spectrale modulateur 3')
xlabel('Fréquence (Hz)')
ylabel('TFD')