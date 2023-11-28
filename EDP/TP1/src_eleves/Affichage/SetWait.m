function [] = SetWait( jvp, n, Kc, KcExp )

global PosWait;
global SizeWait;
global WaitBar;
global PosKc;
global SizeKc;
global KcBar;


present = isempty(PosWait)*isempty(SizeWait)*isempty(WaitBar);
if (present~=0)
   return
end

PosWait(3) = max( fix( (jvp/n)*SizeWait ),  1 );
set( WaitBar, 'Position', PosWait, 'Visible', 'on' );  drawnow;

if (nargin > 2)
    present = isempty(PosKc)*isempty(SizeKc)*isempty(KcBar);
    if (present~=0)
       return
    end

    PosKc(3) = max( fix( (Kc/KcExp)*SizeKc ),  1 );
    set( KcBar, 'Position', PosKc, 'Visible', 'on' );  drawnow;

end
