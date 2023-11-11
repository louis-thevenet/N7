with SDA_Exceptions;         use SDA_Exceptions;

package body TH is
    procedure Initialiser (Sda : out T_TH) is
    begin
        for I in 1..Taille_TH loop
            LCA_TH.Initialiser(Sda(I));
        end loop;
    end Initialiser;

  	procedure Detruire (Sda : in out T_TH) is


    begin
        for I in 1..Taille_TH loop
            LCA_TH.Detruire(Sda(I));
        end loop;
    end Detruire;

function Est_Vide (Sda : T_TH) return Boolean is
    begin
        for I in 1..Taille_TH loop
            if not LCA_TH.Est_Vide(Sda(I)) then return false; end if;
        end loop;
        return true;
    end Est_Vide;


function Taille (Sda : T_TH) return Integer is
    Count : Integer;
begin
Count :=0;
    for I in 1..Taille_TH loop
            Count := Count + LCA_TH.Taille(Sda(I));
        end loop;
        return Count;
end Taille;


procedure Enregistrer (Sda : in out T_TH ; Cle : in T_Cle ; Valeur : in T_Valeur) is
begin
    LCA_TH.Enregistrer(Sda(Hachage(Cle)), Cle, Valeur);
end Enregistrer;

procedure Supprimer (Sda : in out T_TH ; Cle : in T_Cle) is
begin
    LCA_TH.Supprimer(Sda(Hachage(Cle)), Cle);
end Supprimer;

function Cle_Presente (Sda : in T_TH ; Cle : in T_Cle) return Boolean is
begin
    return LCA_TH.Cle_Presente(Sda(Hachage(Cle)), Cle);
end Cle_Presente;

function La_Valeur (Sda : in T_TH ; Cle : in T_Cle) return T_Valeur is
begin
    return LCA_TH.La_Valeur(Sda(Hachage(Cle)), Cle);
end La_Valeur;

procedure Pour_Chaque (Sda : in T_TH) is

procedure Pour_Chaque_LCA is new LCA_TH.Pour_Chaque(Traiter => Traiter);


begin
    for I in 1..Taille_TH loop
        Pour_Chaque_LCA(Sda(I));
    end loop;

end Pour_Chaque;

end TH;




