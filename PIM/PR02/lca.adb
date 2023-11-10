with SDA_Exceptions;         use SDA_Exceptions;
with Ada.Unchecked_Deallocation;

package body LCA is

	procedure Free is
		new Ada.Unchecked_Deallocation (Object => T_Cellule, Name => T_LCA);


	procedure Initialiser(Sda: out T_LCA) is
	begin
		null;	-- TODO : à changer
	end Initialiser;


	procedure Detruire (Sda : in out T_LCA) is
	begin
		null;	-- TODO : à changer
	end Detruire;


	function Est_Vide (Sda : T_LCA) return Boolean is
	begin
		return False;	-- TODO : à changer
	end;


	function Taille (Sda : in T_LCA) return Integer is
	begin
		return 0;	-- TODO : à changer
	end Taille;


	procedure Enregistrer (Sda : in out T_LCA ; Cle : in T_Cle ; Valeur : in T_Valeur) is
	begin
		null;	-- TODO : à changer
	end Enregistrer;


	function Cle_Presente (Sda : in T_LCA ; Cle : in T_Cle) return Boolean is
	begin
		return False;	-- TODO : à changer
	end;


	function La_Valeur (Sda : in T_LCA ; Cle : in T_Cle) return T_Valeur is
	begin
		return 0;	-- TODO : à changer
	end La_Valeur;


	procedure Supprimer (Sda : in out T_LCA ; Cle : in T_Cle) is
	begin
		null;	-- TODO : à changer
	end Supprimer;


	procedure Pour_Chaque (Sda : in T_LCA) is
	begin
		null;	-- TODO : à changer
	end Pour_Chaque;


end LCA;
