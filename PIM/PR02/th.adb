package body TH is
    procedure Initialiser (Sda : out T_TH) is
    begin
        for I in 1..Taille_TH+1 loop
            LCA_TH.Initialiser(Sda(I));
        end loop;
    end Initialiser;

  	procedure Detruire (Sda : in out T_TH) is
    begin
        for I in 1..Taille_TH+1 loop
            LCA_TH.Detruire(Sda(I));
        end loop;
    end Detruire;

function Est_Vide (Sda : T_TH) return Boolean is
    begin
        for I in 1..Taille_TH+1 loop
            if not LCA_TH.Est_Vide(Sda(I)) then return false; end if;
        end loop;
        return true;
    end Est_Vide;


function Taille (Sda : T_TH) return Integer is
    Count : Integer;
begin
Count :=0;
    for I in 1..Taille_TH+1 loop
            Count := Count + LCA_TH.Taille(Sda(I));
        end loop;
        return Count;
end Taille;


procedure Enregistrer (Sda : in out T_TH ; Cle : in T_Cle ; Valeur : in T_Valeur) is
begin
    LCA_TH.Enregistrer(Sda(Hachage(Cle) mod (Taille_TH+1)), Cle, Valeur);
end Enregistrer;

procedure Supprimer (Sda : in out T_TH ; Cle : in T_Cle) is
begin
    LCA_TH.Supprimer(Sda(Hachage(Cle) mod (Taille_TH+1)), Cle);
end Supprimer;

function Cle_Presente (Sda : in T_TH ; Cle : in T_Cle) return Boolean is
begin
    return LCA_TH.Cle_Presente(Sda(Hachage(Cle) mod (Taille_TH+1)), Cle);
end Cle_Presente;

function La_Valeur (Sda : in T_TH ; Cle : in T_Cle) return T_Valeur is
begin
    return LCA_TH.La_Valeur(Sda(Hachage(Cle) mod (Taille_TH+1)), Cle);
end La_Valeur;

procedure Pour_Chaque (Sda : in T_TH) is
    procedure Pour_Chaque_LCA is new LCA_TH.Pour_Chaque(Traiter => Traiter);
begin
    for I in 1..Taille_TH+1 loop
        Pour_Chaque_LCA(Sda(I));
    end loop;

end Pour_Chaque;

procedure Afficher_Debug (Sda : in T_TH) is
    procedure Afficher_Debug_LCA is new LCA_TH.Afficher_Debug(Afficher_Cle, Afficher_Donnee);
begin
    for I in 1..Taille_TH+1 loop
        Afficher_Debug_LCA(Sda(I));
    end loop;
end Afficher_Debug;

end TH;




