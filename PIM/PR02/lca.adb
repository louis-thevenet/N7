with SDA_Exceptions; use SDA_Exceptions;
with Ada.Text_IO; use Ada.Text_IO;
with Ada.Unchecked_Deallocation;

package body LCA is

	procedure Free is
		new Ada.Unchecked_Deallocation (Object => T_Cellule, Name => T_LCA);


	procedure Initialiser(Sda: out T_LCA) is
	begin
		Sda:=Null;
	end Initialiser;


	procedure Detruire (Sda : in out T_LCA) is
	begin
        if Est_Vide(Sda) then
            null;
        else
            Detruire(Sda.All.Suivant);
            Free(Sda);
        end if;
    end Detruire;


	function Est_Vide (Sda : T_LCA) return Boolean is
	begin
        return	Sda = Null;
    end;


	function Taille (Sda : in T_LCA) return Integer is
	begin
        if Est_Vide(Sda) then
            return 0;
        else
            return 1 + Taille(Sda.All.Suivant);
        end if;
	end Taille;


	procedure Enregistrer (Sda : in out T_LCA ; Cle : in T_Cle ; Valeur : in T_Valeur) is
	begin
		if Est_Vide(Sda) then
            Sda := new T_Cellule'(Cle, Valeur, Null);
        elsif Sda.All.Cle = Cle then
            Sda.All.Valeur := Valeur;
        else
            Enregistrer(Sda.All.Suivant, Cle, Valeur);
        end if;
	end Enregistrer;


    function Maillon_Existe(Sda : in T_LCA; Cle : in T_Cle) return T_LCA is
    begin
        if Est_Vide(Sda) then
            return Null;
        elsif Sda.All.Cle = Cle then
            return Sda;
        else
            return Maillon_Existe(Sda.All.Suivant,Cle);
        end if;
    end Maillon_Existe;

	function Cle_Presente (Sda : in T_LCA ; Cle : in T_Cle) return Boolean is
    Tmp : T_LCA;
	begin
		Tmp := Maillon_Existe(Sda, Cle);
        if Est_Vide(Tmp) then
            return false;
        else
            return true;
        end if;
	end Cle_Presente;


	function La_Valeur (Sda : in T_LCA ; Cle : in T_Cle) return T_Valeur is
    Tmp : T_LCA;
	begin
		Tmp := Maillon_Existe(Sda, Cle);
        if Est_Vide(Tmp) then
            raise Cle_Absente_Exception;
        else
            return La_Valeur(Sda.All.Suivant, Cle);
        end if;
	end La_Valeur;


	procedure Supprimer (Sda : in out T_LCA ; Cle : in T_Cle) is
    Tmp : T_LCA;
	begin
		if Est_Vide(Sda) then
            raise Cle_Absente_Exception;
        end if;

        if Sda.All.Cle = Cle then
            Tmp:= Sda;
            Sda := Sda.All.Suivant;
            Free(Tmp);
        else
            if Est_Vide(Sda.All.Suivant) then
                raise Cle_Absente_Exception;
            else
                if Sda.All.Suivant.All.Cle = Cle then
                    Tmp := Sda.All.Suivant.All.Suivant;

                    Free(Sda.All.Suivant);
                    Sda.All.Suivant := Tmp;
                else
                    Supprimer(Sda.All.Suivant, Cle);
                end if;
            end if;
        end if;
	end Supprimer;


	procedure Pour_Chaque (Sda : in T_LCA) is
	begin
		if Est_Vide(Sda) then
            return;
        else
            null;
        end if;

        begin
            Traiter(Sda.All.Cle, Sda.All.Valeur);
            exception
                when others => null;
        end;

        Pour_Chaque(Sda.All.Suivant);

	end Pour_Chaque;

   	procedure Afficher_Debug (Sda : in T_LCA) is
    begin
        if (Est_Vide(Sda)) then
            Put("--E");
            return;
        end if;
        Put("-->[");
        Afficher_Cle(Sda.All.Cle);
        Put(":");
        Afficher_Donnee(Sda.All.Valeur);
        Put("]");
        Afficher_Debug(Sda.All.Suivant);
    end Afficher_Debug;



end LCA;
