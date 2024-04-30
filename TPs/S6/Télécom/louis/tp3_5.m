%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                   TP3 de Télécommunications
%                   SCIENCES DU NUMERIQUE 1A
%                           Avril 2024
%                        Louis Thevenet
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

clear all
close all

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%PARAMETRES GENERAUX
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
Nb=10000;       %nombres de bits générés
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
Nsb_1 = Nb/log2(M);

%mapping
ak = 2*bits-1;

%surréchantillonage des bits
suite_diracs = kron(ak,[1 zeros(1,Ns_1-1)]);

%mise en place du filtre
B=ones(1,Ns_1);
x=filter(B,1,suite_diracs);

% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% % AJOUT D'UN BRUIT
% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% SNR = 1000;
% 
% %Signal 1 et 2
% Px = mean(abs(x).^2);
% sigma2 = (Px*Nsb_1)/(2*log2(M)*SNR);
% bruit = sqrt(sigma2)*randn(1,length(x));
% x = x+bruit;

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% DEMODULATEUR 1
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Signal demodulé par le filtre de reception (meme que celui de mise en forme)
x1_demodule = filter(B,1,x);

g1 = conv(B,B);

figure
plot(g1);
xlabel('Echantillons')
ylabel('g')
title('Réponse impulsionelle globale de la chaine de transmission 1')

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% DEMODULATEUR 2
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Signal demodulé par le filtre de reception filtre de réception rectangulaire de durée égale à la
%moitié de la période symbole et de hauteur 1
B2=ones(1,Ns_1/2);
x2_demodule = filter(B2,1,x);

g2 = conv(B,B2);

figure
plot(g2);
xlabel('Echantillons')
ylabel('g')
title('Réponse impulsionelle globale de la chaine de transmission 2')

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

%surréchantillonage des bits
suite_diracs2 = kron(ak2',[1 zeros(1,Ns_2-1)]);

%mise en place du filtre
B=ones(1,Ns_2);
x2=filter(B,1,suite_diracs2);

% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% % AJOUT D'UN BRUIT
% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% SNR = 100;
%
% %Signal 3
% Px = mean(abs(x2).^2);
% sigma2 = (Px*Nsb_2)./(2*log2(M)*SNR);
% bruit = sqrt(sigma2)*randn(1,length(x2));
% x2 = x2 + bruit;

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% DEMODULATEUR 3
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Signal demodulé par le filtre de reception (meme que celui de mise en forme)
x3_demodule = filter(B,1,x2);

g3 = conv(B,B);

figure
plot(g3);
xlabel('Echantillons')
ylabel('g')
title('Réponse impulsionelle globale de la chaine de transmission 3')

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% DIAGRAMMES DE L'OEIL
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
figure
plot(reshape(x1_demodule,Ns_1,length(x1_demodule)/Ns_1))
title('Diagramme de l oeil 1')

figure
plot(reshape(x2_demodule,Ns_1,length(x2_demodule)/Ns_1))
title('Diagramme de l oeil 2')

figure
plot(reshape(x3_demodule,Ns_2,length(x3_demodule)/Ns_2))
title('Diagramme de l oeil 3')

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TAUX D'ERREUR BINAIRE (TEB)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%décalage avec les instants optimaux
x1_demodule_decalage = x1_demodule(8:Ns_1:end);
x2_demodule_decalage = x2_demodule(4:Ns_1:end);
x3_demodule_decalage = x3_demodule(16:Ns_2:end)/16;

%seuils optimaux de décision
K1 = 0;
K2 = 0;

%détection de seuil
bits_sortis1 = x1_demodule_decalage > K1;
nb_bits_erreur1 = sum(bits_sortis1 ~= bits);

bits_sortis2 = x2_demodule_decalage > K2;
nb_bits_erreur2 = sum(bits_sortis2 ~= bits);


%Taux d'erreur binaire
TEB1 = nb_bits_erreur1/Nb
TEB2 = nb_bits_erreur2/Nb


%(pour tout anoté control R pui control maj R)
% %%
xr_temp = zeros(1,Nb/2);
xr_temp(x3_demodule_decalage>=2)=3;
xr_temp(x3_demodule_decalage<2 & x3_demodule_decalage>0)=1;
xr_temp(x3_demodule_decalage<=0 & x3_demodule_decalage>-2)=-1;
xr_temp(x3_demodule_decalage<=-2)=-3;

xr = [];
for i=1:Nb/2
    if xr_temp(i)== -3
        xr = [xr 0 0];
    elseif xr_temp(i)== -1
        xr = [xr 1 0];
    elseif xr_temp(i)== 1
        xr = [xr 0 1];
    else
        xr = [xr 1 1];
    end

end

TEB3 = mean(xr ~= bits)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% MODULATEUR 1 avec un bruit
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

M=2;
Ts_1 = Tb*log2(M);  %période symbole
Rs_1 = 1/Ts_1;      %débit symbole
Ns_1 = Ts_1/Te;
Nsb_1 = Nb/log2(M);

%mapping
ak = 2*bits-1;

%surréchantillonage des bits
suite_diracs = kron(ak,[1 zeros(1,Ns_1-1)]);

%mise en place du filtre
B=ones(1,Ns_1);

TEB1=ones(1,8);

for i=1:8
    x=filter(B,1,suite_diracs);
    Px = mean(abs(x).^2);
    Eb_n0=10^(i/10);
    sigma2 = (Px*Ns_1)/(2*log2(M)*Eb_n0);
    bruit = sqrt(sigma2)*randn(1,length(x));
    x = x + bruit;
    x1_demodule = filter(B,1,x);
    x1_demodule_decalage = x1_demodule(8:Ns_1:end);
    bits_sortis1 = x1_demodule_decalage > 0;
    nb_bits_erreur1 = sum(bits_sortis1 ~= bits);
    TEB1(i) = nb_bits_erreur1/Nb;

end

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TEB THEORIQUE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%TEB = Q(sqrt(2*Eb/N0))
SNR = [1:1:8];
Eb_n0=10.^(SNR/10);
TEBT = qfunc(sqrt(2*Eb_n0));

%tracé du signal 1
figure
semilogy(SNR,TEBT,'b')
hold on
semilogy(SNR,TEB1,'r')
grid
legend('TEB théorique','TEB simulé')
xlabel('SNR')
title('Tracé des TEB du signal avec le modulateur 1')

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% MODULATEUR 2 avec un bruit
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

M=2;
Ts_1 = Tb*log2(M);  %période symbole
Rs_1 = 1/Ts_1;      %débit symbole
Ns_1 = Ts_1/Te;
Nsb_1 = Nb/log2(M);

%mapping
ak = 2*bits-1;

%surréchantillonage des bits
suite_diracs = kron(ak,[1 zeros(1,Ns_1-1)]);

%mise en place du filtre
B=ones(1,Ns_1);
x=filter(B,1,suite_diracs);

TEB2=ones(1,8);

for i=1:8
    x = filter(B,1,suite_diracs);
    Px = mean(abs(x).^2);
    Eb_n0=10^(i/10);
    sigma2 = (Px*Ns_1)/(2*log2(M)*Eb_n0);
    bruit = sqrt(sigma2)*randn(1,length(x));
    x = x+bruit;
    B2=ones(1,Ns_1/2);
    x2_demodule = filter(B2,1,x);
    x2_demodule_decalage = x2_demodule(4:Ns_1:end);
    bits_sortis2 = x2_demodule_decalage > 0;
    nb_bits_erreur2 = sum(bits_sortis2 ~= bits);
    TEB2(i) = nb_bits_erreur2/Nb;
end


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TEB THEORIQUE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%TEB = Q(sqrt(2*Eb/N0))
SNR = [1:1:8];
Eb_n0=10.^(SNR/10);
TEBT = qfunc(sqrt(Eb_n0));

%tracé du signal 2
figure
semilogy(SNR,TEBT,'b')
hold on
semilogy(SNR,TEB2,'r')
grid
legend('TEB théorique', 'TEB simulé')
xlabel('Eb_n0')
title('Tracé des TEB du signal avec le modulateur 2')

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%MODULATEUR 3 avec un bruit
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
M=4;
Ts_2 = Tb*log2(M);  %période symbole
Rs_2 = 1/Ts_2;      %débit symbole
Ns_2 = Ts_2/Te;
Nsb_2 = Nb/log2(M);

%mapping
entiers = bi2de(reshape(bits,2,Nb/2)');
ak2 = pammod(entiers,M);

%surréchantillonage des bits
suite_diracs2 = kron(ak2',[1 zeros(1,Ns_2-1)]);

%mise en place du filtre
B=ones(1,Ns_2);

TEB3 = ones(1,8);

for i=1:8
    x2=filter(B,1,suite_diracs2);
    Px = mean(abs(x2).^2);
    Eb_n0=10^(i/10);
    sigma2 = (Px*Ns_2)./(2*log2(M)*Eb_n0);
    bruit = sqrt(sigma2)*randn(1,length(x2));
    x2 = x2 + bruit;
    x3_demodule = filter(B,1,x2);
    x3_demodule_decalage=x3_demodule(16:Ns_2:end)/16;
    xr_temp = zeros(1,Nb/2);
    xr_temp(x3_demodule_decalage>=2)=3;
    xr_temp(x3_demodule_decalage<2 & x3_demodule_decalage>0)=1;
    xr_temp(x3_demodule_decalage<=0 & x3_demodule_decalage>-2)=-1;
    xr_temp(x3_demodule_decalage<=-2)=-3;

    xr = [];
    for j=1:Nb/2
        if xr_temp(j)== -3
            xr = [xr 0 0];
        elseif xr_temp(j)== -1
            xr = [xr 1 0];
        elseif xr_temp(j)== 1
            xr = [xr 0 1];
        else
            xr = [xr 1 1];
        end

    end

    TEB3(i) = mean(xr ~= bits);
end

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TEB THEORIQUE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%TEB = Q(sqrt(2*Eb/N0))
SNR = [1:1:8];
%TEBT = 3/2*qfunc(sqrt(2*SNR/(Ns_2*3)));
Eb_n0=10.^(SNR/10);
TEBT = qfunc(sqrt(4/5*Eb_n0));

%tracé du signal 2
figure
semilogy(SNR,TEBT,'b')
hold on
semilogy(SNR,TEB3,'r')
grid
legend('TEB théorique', 'TEB simulé')
xlabel('Eb/N0')
title('Tracé des TEB du signal avec le modulateur 3')

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TEB SIMULE 1 ET 2
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

figure
semilogy(SNR,TEB1,'b')
hold on
semilogy(SNR,TEB2,'r')
grid
legend('TEB1', 'TEB2')
xlabel('Eb/N0')
title('Tracé des TEBs simulés 1 et 2')

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TEB SIMULE 1 ET 3
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

figure
semilogy(SNR,TEB1,'b')
hold on
semilogy(SNR,TEB3,'r')
grid
legend('TEB1', 'TEB3')
xlabel('Eb/N0')
title('Tracé des TEBs simulés 1 et 3')

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%MODULATEUR 3 avec un bruit et mapping de gray
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
M=4;
Ts_2 = Tb*log2(M);  %période symbole
Rs_2 = 1/Ts_2;      %débit symbole
Ns_2 = Ts_2/Te;
Nsb_2 = Nb/log2(M);

%mapping
entiers = bi2de(reshape(bits,2,Nb/2)');
ak2 = pammod(entiers,M, 0, 'gray');

%surréchantillonage des bits
suite_diracs2 = kron(ak2',[1 zeros(1,Ns_2-1)]);

%mise en place du filtre
B=ones(1,Ns_2);

TEB3 = ones(1,8);

for i=1:8
    x2=filter(B,1,suite_diracs2);
    Px = mean(abs(x2).^2);
    Eb_n0=10^(i/10);
    sigma2 = (Px*Ns_2)./(2*log2(M)*Eb_n0);
    bruit = sqrt(sigma2)*randn(1,length(x2));
    x2 = x2 + bruit;
    x3_demodule = filter(B,1,x2);
    x3_demodule_decalage=x3_demodule(16:Ns_2:end)/16;
    xr_temp = zeros(1,Nb/2);
    xr_temp(x3_demodule_decalage>=2)=3;
    xr_temp(x3_demodule_decalage<2 & x3_demodule_decalage>0)=1;
    xr_temp(x3_demodule_decalage<=0 & x3_demodule_decalage>-2)=-1;
    xr_temp(x3_demodule_decalage<=-2)=-3;

    xr = [];
    for j=1:Nb/2
        if xr_temp(j)== -3
            xr = [xr 0 0];
        elseif xr_temp(j)== -1
            xr = [xr 1 0];
        elseif xr_temp(j)== 1
            xr = [xr 1 1];
        else
            xr = [xr 0 1];
        end

    end

    TEB3(i) = mean(xr ~= bits)
end

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TEB THEORIQUE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%TEB = Q(sqrt(2*Eb/N0))
SNR = [1:1:8];
%TEBT = 3/2*qfunc(sqrt(2*SNR/(Ns_2*3)));
Eb_n0=10.^(SNR/10);
TEBT = 3/4*qfunc(sqrt((4/5)*Eb_n0));

%tracé du signal 2
figure
semilogy(SNR,TEBT,'b')
hold on
semilogy(SNR,TEB3,'r')
grid
legend('TEB théorique', 'TEB simulé')
xlabel('Eb/N0')
title('Tracé des TEB du signal avec le modulateur 3 avec le mapping de Gray')