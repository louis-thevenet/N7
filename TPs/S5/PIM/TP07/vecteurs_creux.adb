with Ada.Text_IO;                 use Ada.Text_IO;
with Ada.Integer_Text_IO;         use Ada.Integer_Text_IO;
with Ada.Float_Text_IO;           use Ada.Float_Text_IO;
with Ada.Unchecked_Deallocation;

package body Vecteurs_Creux is


	procedure Free is
		new Ada.Unchecked_Deallocation (T_Cellule, T_Vecteur_Creux);


	procedure Initialiser (V : out T_Vecteur_Creux) is
	begin
        V := Null;
	end Initialiser;


	procedure Detruire (V: in out T_Vecteur_Creux) is
	begin
        if Est_Nul(V) then
            return;
        else
            Detruire(V.All.Suivant);
            Free(V);
        end if;
	end Detruire;


	function Est_Nul (V : in T_Vecteur_Creux) return Boolean is
	begin
		return V=Null;
	end Est_Nul;


	function Composante_Recursif (V : in T_Vecteur_Creux ; Indice : in Integer) return Float is
	begin
        if Est_Nul(V) then
            return 0.0;
        elsif Indice = V.All.Indice then
            return V.All.Valeur;
        else
            return Composante_Recursif(V.All.Suivant, Indice);
        end if;
	end Composante_Recursif;


	function Composante_Iteratif (V : in T_Vecteur_Creux ; Indice : in Integer) return Float is
    tmp : T_Vecteur_Creux;
	begin
        tmp := V;
        While (True) loop
            if (Est_Nul(tmp)) then
                return 0.0;
            elsif (tmp.All.Indice = Indice) then
                return tmp.All.Valeur;
            elsif tmp.All.Indice > Indice then
                return 0.0;
            end if;
            tmp:=tmp.All.Suivant;
        end loop;
        return 0.0;
	end Composante_Iteratif;


	procedure Modifier (V : in out T_Vecteur_Creux ;
				       Indice : in Integer ;
					   Valeur : in Float ) is
tmp : T_Vecteur_Creux;
	begin
        if Est_Nul(V) then
            V := new T_Cellule;
            V.All.Indice := Indice;
            V.All.Valeur :=Valeur;
            V.All.Suivant:=Null;

        elsif (Indice = V.All.Indice) then
            V.All.Valeur := Valeur;

        elsif (Indice < V.All.Indice ) then
            tmp := new T_Cellule;
            tmp.All := V.All;

            V.All.Indice := Indice;
            V.All.Valeur := Valeur;
            V.All.Suivant := tmp;
        elsif Est_Nul(V.All.Suivant) then

            V.All.Suivant := new T_Cellule;
            V.All.Suivant.All.Indice := Indice;
            V.All.Suivant.All.Valeur :=Valeur;
            V.All.Suivant.All.Suivant:=Null;
        else
            Modifier(V.All.Suivant, Indice, Valeur);
        end if;
	end Modifier;


	function Sont_Egaux_Recursif (V1, V2 : in T_Vecteur_Creux) return Boolean is
    begin
        if Est_Nul(V1) xor Est_Nul(V2) then
            return false;
        end if;
        if Est_Nul(V1) and then Est_Nul(V2) then
            return true;
        end if;

        return V1.All.Valeur = V2.All.Valeur
            and then V1.All.Indice = V2.All.Indice
            and then Sont_Egaux_Recursif(V1.All.Suivant, V2.All.Suivant);
	end Sont_Egaux_Recursif;


	function Sont_Egaux_Iteratif (V1, V2 : in T_Vecteur_Creux) return Boolean is

    tmp, tmp2 : T_Vecteur_Creux;
	begin
        tmp := V1;
        tmp2 := V2;
        While (True) loop
            if (Est_Nul(tmp) xor Est_Nul(tmp2)) then
                return false;
            elsif (Est_Nul(tmp) and Est_Nul(tmp2)) then
                return true;
            end if;
            if (tmp.All.Indice = tmp2.All.Indice  and then tmp.All.Valeur=tmp2.All.Valeur) then
                tmp := tmp.All.Suivant;
                tmp2:=tmp2.All.Suivant;
            else
                return false;
            end if;
        end loop;
	end Sont_Egaux_Iteratif;


	procedure Additionner (V1 : in out T_Vecteur_Creux; V2 : in T_Vecteur_Creux) is
	Res, tmp, tmp2 : T_Vecteur_Creux;

	begin
        tmp := V1;
        tmp2 := V2;
        Initialiser(Res);
        While (True) loop
            if (Est_Nul(tmp) and Est_Nul(tmp2)) then
                return;
            end if;
            if Est_Nul(tmp) or else tmp.All.Indice > tmp2.All.indice then
                Modifier(V1, tmp2.All.Indice, tmp2.All.Valeur);
                tmp2:=tmp2.All.Suivant;
            elsif Est_Nul(tmp2) or else tmp.All.Indice < tmp2.All.indice then
                Modifier(V1, tmp.All.Indice, tmp.All.Valeur);
                tmp:=tmp.All.Suivant;
            else
                Modifier(V1, tmp2.Indice, tmp.All.Valeur + tmp2.All.Valeur);
                tmp2:=tmp2.All.Suivant;
                tmp:=tmp.All.Suivant;
            end if;
        end loop;

	end Additionner;


	function Norme2 (V : in T_Vecteur_Creux) return Float is
    tmp : T_Vecteur_Creux;
    Res : Float;
	begin
        tmp := V;
        while (True) loop
            if Est_Nul(tmp) then
                return Res;
            end if;
            Res := Res + tmp.All.Valeur * tmp.All.Valeur;
            tmp := tmp.All.Suivant;
        end loop;
    end Norme2;


	Function Produit_Scalaire (V1, V2: in T_Vecteur_Creux) return Float is
	tmp, tmp2 : T_Vecteur_Creux;
    Somme : Float;
	begin
        tmp := V1;
        tmp2 := V2;
        Somme := 0.0;
        While (True) loop
            if (Est_Nul(tmp) and Est_Nul(tmp2)) then
                return Somme;
            end if;
            if Est_Nul(tmp) then
                tmp2:=tmp2.All.Suivant;
            elsif Est_Nul(tmp2) then
                tmp:=tmp.All.Suivant;
            else
                Somme := Somme+tmp.All.Valeur*tmp2.All.Valeur;
                tmp2:=tmp2.All.Suivant;
                tmp:=tmp.All.Suivant;
            end if;
        end loop;
    end Produit_Scalaire;


	procedure Afficher (V : T_Vecteur_Creux) is
	begin
		if V = Null then
			Put ("--E");
		else
			-- Afficher la composante V.all
			Put ("-->[ ");
			Put (V.all.Indice, 0);
			Put (" | ");
			Put (V.all.Valeur, Fore => 0, Aft => 1, Exp => 0);
			Put (" ]");

			-- Afficher les autres composantes
			Afficher (V.all.Suivant);
		end if;
	end Afficher;


	function Nombre_Composantes_Non_Nulles (V: in T_Vecteur_Creux) return Integer is
	begin
		if V = Null then
			return 0;
		else
			return 1 + Nombre_Composantes_Non_Nulles (V.all.Suivant);
		end if;
	end Nombre_Composantes_Non_Nulles;


end Vecteurs_Creux;
