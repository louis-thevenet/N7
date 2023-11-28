global PosWait;
global SizeWait;
global WaitBar;

present = isempty(PosWait)*isempty(SizeWait)*isempty(WaitBar);
if (present==0)
   clear Hfig        KcFrame     WaitFrame   black       fig         fy4         lightgreen  orange      red         whitepaper
   clear KcBar       PosKc       SizeKc      WaitLabel   blue        fx4         lightblue   magenta     pink        white
   close(10)
end

PosWait = '';  SizeWait = '';  WaitBar = '';
clear PosWait SizeWait WaitBar present