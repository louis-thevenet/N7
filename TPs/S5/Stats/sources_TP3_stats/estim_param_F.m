% Fonction estim_param_F (exercice_1.m)

function [rho_F,theta_F,ecart_moyen] = estim_param_F(rho,theta)


A = [cos(theta), sin(theta)];
F  = A\  rho;
rho_F = sqrt(F(1)*F(1) + F(2)*F(2));

theta_F = atan2(F(2), F(1));

%ecart_moyen = mean(rho - rho_F*cos(theta-theta_F));
ecart_moyen = mean(abs(A*F - rho));

end