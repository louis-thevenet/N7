%% Chaine 1
N=20;
M = 2; % Code 2 symboles (2^n)
Rs1 = Rb/log2(M);
Ns1 = 1/(Te*Rs1); % Nombre d'échantillons par symbole
Ts1 = 1/Rs1;
 
% Bits
bits1 = randi([0,1], 1, N); % Entre 0 et 1
 
% Mapping binaire à moyenne nulle
map1 = (bits1.*2) - 1; % Entre -1 et 1
 
% Suréchantillonnage
B = zeros(length(temps), 1);
B(1:Ns1:end) = map;
 
% Filtre de  mise en forme rectangulaire de durée égale à la période symbole
h1 = ones(1, Ns1);
x1 = filter(h1, 1, B);
 
% Filtre de réception
hr1 = ones(1, Ns1);
yr1 = filter(hr1,1,x1);
 
% Chaine de transmission
figure;
g1 = conv(h1 ,hr1); % Pas de canal
 
% Convolution de 2 portes ==> Triangle
t_g1 = linspace(0,2*Ns1,length(g1));
subplot(2, 1, 1);
plot(t_g1,g1)
ylim([-10,10])
title("Réponse impulsionnelle globale de la chaine 1");
xlabel('Temps ');
ylabel("g1(t)");
axis([0 2*Ns1 0 10]);
 
% Diagramme de l'oeil
oeil1 = reshape(yr1,Ns1,length(yr1)/Ns1);
to1 = linspace(0,Ns1,size(oeil1,1));
subplot(2, 1, 2);
plot(to1,oeil1)
xlabel('Temps ')
ylabel('Amplitude')
title("Diagramme de l'oeil 1");
 
%% Chaine 2 
 
M = 2; % Code 2 symboles (2^n)
Rs2 = Rb/log2(M);
Ns2 = 1/(Te*Rs2); % Nombre d'échantillons par symbole
Ts2 = 1/Rs2;
 
% Bits
bits2 = randi([0,1], 1, N); % Entre 0 et 1
 
% Mapping binaire à moyenne nulle
map2 = (bits2.*2) - 1; % Entre -1 et 1
 
% Suréchantillonnage
B = zeros(length(temps), 1);
B(1:Ns1:end) = map;
 
% Filtre de  mise en forme rectangulaire de durée égale à la période symbole
h2 = ones(1, Ns2);
x2 = filter(h2, 1, B);
 
% Filtre de réception
hr2 = ones(1, Ns2/2);
yr2 = filter(hr2,1,x2);
 
% Chaine de transmission
figure;
g2 = conv(h2 ,hr2); % Pas de canal
 
% Convolution de 2 portes ==> Triangle
t_g2 = linspace(0,2*Ns2,length(g2));
subplot(2, 1, 1);
plot(t_g2,g2)
ylim([-10,10])
title("Réponse impulsionnelle globale de la chaine 2");
xlabel('Temps ');
ylabel("g2(t)");
axis([0 2*Ns2 0 10]);
 
% Diagramme de l'oeil 2
oeil2 = reshape(yr2,Ns2,length(yr2)/Ns2);
to2 = linspace(0,Ns2,size(oeil2,1));
subplot(2, 1, 2);
plot(to2, oeil2);
xlabel('Temps ');
ylabel('Amplitude');
title("Diagramme de l'oeil 2");
 
 
%% Chaine 3
 
M = 4; % Code 2 symboles (2^n)
Rs3 = Rb/log2(M);
Ns3 = 1/(Te*Rs3); % Nombre d'échantillons par symbole
Ts3 = 1/Rs3;
 
% Bits
bits3 = randi([0,1], 1, N); % Entre 0 et 1
 
% Mapping binaire à moyenne nulle
map3 = reshape(bits3, N/2, 2);
map3 = bi2de(map3);
map3 = map3*2 - 3;
 
% Suréchantillonnage
B = zeros(length(temps), 1);
B(1:Ns3:end) = map3;
 
% Filtre de mise en forme
h3 = ones(1, Ns3);
y3 = filter(h3, 1, B);
 
%%%%%%%%%%%% A FINIR DEPUIS ICI
 
% Filtre de réception
hr3 = ones(1, Ns3);
yr3 = filter(hr3,1,x3);
 
% Chaine de transmission
figure;
g3 = conv(h3 ,hr3); % Pas de canal
 
% Convolution de 2 portes ==> Triangle
t_g3 = linspace(0,2*Ns3,length(g3));
subplot(2, 1, 1);
plot(t_g3,g3)
ylim([-10,10])
title("Réponse impulsionnelle globale de la chaine 3");
xlabel('Temps ');
ylabel("g3(t)");
axis([0 2*Ns3 0 10]);
 
% Diagramme de l'oeil 3
oeil3 = reshape(yr3,Ns3,length(yr3)/Ns3);
to3 = linspace(0,Ns3,size(oeil3,1));
subplot(2, 1, 2);
plot(to3, oeil3);
xlabel('Temps ');
ylabel('Amplitude');
title("Diagramme de l'oeil 3");