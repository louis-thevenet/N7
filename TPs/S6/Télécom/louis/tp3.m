
Fe = 24000;
Te = 1/Fe;
Rb = 3000;
Tb = 1/Rb;
n=1;
M = 2^n;
Ts = log2(M)*Tb;
Rs = Rb/log2(M);
nb_bits = 2048;
S = randi([0 1],nb_bits,1);

SNR = 300;
bruit = false

%% modulateur 1 :
% Mapping

Ns = Fe * Ts; % Nombre d'échantillons par bits

SE = (2*S - 1)'; % enter -1 et 1
At = kron(SE, [1 zeros(1, Ns-1)]); % suréchantillonage

% Filtre
T1 = 0:Te:(nb_bits*Ns-1)*Te; % Echelle temporelle
h1 = ones(1, Ns); % Reponse impulsionnelle du filtre
y = filter(h1, 1, At);

% Tracés
figure('name', 'Modulateur 1')

    % Signal généré
    nexttile
    stem(T1,At)
    ylim([-1.5, 1.5])
    xlabel("temps (s)")
    ylabel("Signal temporel")
    title('Tracé du signal temporel');

    nexttile
    plot(T1,y)
    ylim([-1.5, 1.5])
    xlabel("temps (s)")
    ylabel("Signal filtré")
    title('Tracé du signal temporel filtré')
%bruit
if bruit
    Px = mean(abs(y).^2);
    sigma2 = (Px * Ns)/(2*log2(M)*SNR);
    bruit = sqrt(sigma2) * randn(1, length(y));
    y = y+bruit;
end
% filtre récéption
y = filter(h1,1,y);
    plot(T1,y)
    ylim([-10,10]);
    xlabel("temps (s)")
    ylabel("Signal filtré")
    title('Tracé du signal temporel filtré à la récéption')
% réponse globale impulsion

g = conv(h1,h1);
t_g = linspace(0,2*Ns,length(g));
figure ('name','réponse impulsionelle globale 1')
plot(t_g,g)
    ylim([-10,10])
    xlabel("temps (s)")
    ylabel("g(t)")
    title('réponse impulsionelle globale')

% Diagramme de l'oeil
oeil = reshape(y,Ns,length(y)/Ns);
to= linspace(0,Ns,size(oeil,1));
figure
plot(to,oeil)
xlabel('temps')
ylabel('amplitude')
title('diagramme de l''oeil 1')

N0=floor(Ts*Fe);
xe = y(N0:Ns:length(y));
xr = zeros(1,length(S));
xr(xe>0)=1;
xr(xe<0)=0;


TEB = mean(S' ~= xr)

%% modulateur 2 :
% Mapping

Ns = Fe * Ts; % Nombre d'échantillons! par bits

SE = (2*S - 1)';
At = kron(SE, [1 zeros(1, Ns-1)]);

% Filtre
T1 = 0:Te:(nb_bits*Ns-1)*Te; % Echelle temporelle
h1 = ones(1, Ns); % Reponse impulsionnelle du filtre
y = filter(h1, 1, At);

% Tracés
figure('name', 'Modulateur 2 ')

    % Signal généré
    nexttile
    stem(T1,At)
    ylim([-1.5, 1.5])
    xlabel("temps (s)")
    ylabel("Signal temporel")
    title('Tracé du signal temporel');

    nexttile
    plot(T1,y)
    ylim([-1.5, 1.5])
    xlabel("temps (s)")
    ylabel("Signal filtré")
    title('Tracé du signal temporel filtré')

%bruit
if bruit
    Px = mean(abs(y).^2);
    sigma2 = (Px * Ns)/(2*log2(M)*SNR);
    bruit = sqrt(sigma2) * randn(1, length(y));
    y = y+bruit;
end

% filtre récéption
hr = ones(1,Ns/2);
y = filter(hr,1,y);
    plot(T1,y)
    ylim([-10,10]);
    xlabel("temps (s)")
    ylabel("Signal filtré")
    title('Tracé du signal temporel filtré à la récéption')
% réponse globale impulsion

g = conv(h1,hr);
t_g = linspace(0,2*Ns,length(g));
figure ('name','réponse impulsionelle globale')
plot(t_g,g)
    ylim([-10,10])
    xlabel("temps (s)")
    ylabel("g(t)")
    title('réponse impulsionelle globale 2')

% Diagramme de l'oeil
oeil = reshape(y,Ns,length(y)/Ns);
to= linspace(0,Ns,size(oeil,1));
figure
plot(to,oeil)
xlabel('temps')
ylabel('amplitude')
title('diagramme de l''oeil 2')

N0=floor(Ts*Fe);
xe = y(N0:Ns:length(y));
xr = zeros(1,length(S));
xr(xe>0)=1;
xr(xe<0)=0;


TEB = mean(S' ~= xr)

%% modulateur 3 :
% Mapping
n=2;
M=2^2;
Ns = Fe * 2*Ts; % Nombre d'échantillons par bits

S2 = reshape(S',2,nb_bits/2);
S2E = [1, nb_bits/2];
Choix = [-3 -1; 1 3];
for i=1:size(S2,2)
    S2E(i) = Choix(S2(1,i)+1,S2(2,i)+1);
end
At = kron(S2E, [1, zeros(1, Ns-1)]);

% Filtre
T1 = 0:Te:(nb_bits*Ns-1)*Te/2; % Echelle temporelle
h1 = ones(1, Ns); % Reponse impulsionnelle du filtre
y = filter(h1, 1, At);

% Tracés
figure('name', 'Modulateur 3 ')

    % Signal généré
    nexttile
    stem(T1,At)
    ylim([-3.5, 3.5])
    xlabel("temps (s)")
    ylabel("Signal temporel")
    title('Tracé du signal temporel');

    nexttile
    plot(T1,y)
    ylim([-3.5, 3.5])
    xlabel("temps (s)")
    ylabel("Signal filtré")
    title('Tracé du signal temporel filtré')

%bruit
if bruit
    Px = mean(abs(y).^2);
    sigma2 = (Px * Ns)/(2*log2(M)*SNR);
    bruit = sqrt(sigma2) * randn(1, length(y));
    y = y+bruit;
end

% filtre récéption
hr = ones(1,Ns);
y = filter(hr,1,y);
    plot(T1,y)
    ylim([-64,64]);
    xlabel("temps (s)")
    ylabel("Signal filtré")
    title('Tracé du signal temporel filtré à la récéption')

% réponse globale impulsion
g = conv(h1,hr);
t_g = linspace(0,2*Ns,length(g));
figure ('name','réponse impulsionelle globale 3')
plot(t_g,g)

    xlabel("temps (s)")
    ylabel("g(t)")
    title('réponse impulsionelle globale')

% Diagramme de l'oeil
oeil = reshape(y,Ns,length(y)/Ns);
to= linspace(0,Ns,size(oeil,1));
figure
plot(to,oeil)
xlabel('temps')
ylabel('amplitude')
title('diagramme de l''oeil 3')

N0=floor(2*Ts*Fe);

xe = y(N0:Ns:length(y))/16;
xr_temp = zeros(1,length(S)/2);
xr_temp(xe>2)=3;
xr_temp(xe<=2 & xe>0)=1;
xr_temp(xe<=0 & xe>-2)=-1;
xr_temp(xe<=-2)=-3;

xr = [];
for i=1:length(S)/2
    if xr_temp(i)== -3
        xr = [xr 0 0];
    elseif xr_temp(i)== -1
        xr = [xr 0 1];
    elseif xr_temp(i)== 1
        xr = [xr 1 0];
    else
        xr = [xr 1 1];
    end

end

TEB = mean(S' ~= xr)