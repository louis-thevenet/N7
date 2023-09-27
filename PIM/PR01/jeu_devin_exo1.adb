with Text_Io;              use Text_Io;
with Ada.Integer_Text_Io;  use Ada.Integer_Text_Io;
with Alea;

-- Auteur : Louis THEVENET

procedure Jeu_Devin_Exo1 is
	-- Jouer au jeu du devin en faisant deviner le nombre à l'utilisateur
	package Mon_Alea is new Alea (1, 999);
	use Mon_Alea;

	function Traiter_Proposition(Nombre_A_Deviner: in Integer; Choix: in Integer) return Boolean
	is
		Fini: Boolean;
	begin
		if Nombre_A_Deviner = Choix then
			Put("Trouvé");
			return true;
		elsif Nombre_A_Deviner < Choix then
			Put ("Trop grand.");
			return false;
		else 
			Put("Trop petit.");
			return false;
		end if;
	end Traiter_Proposition;

	Nombre_A_Deviner, Coups, Choix: Integer;
	Fini: Boolean;
begin
	Get_Random_Number(Nombre_A_Deviner);
	Put ("J'ai choisi un nombre entre 1 et 999.");
	Coups := 1;

	while not Fini loop
		New_Line;
		Put ("Proposition ");
		Put (coups, 1);
		Put(" : ");
		Get (Choix);
		Fini := Traiter_Proposition(Nombre_A_Deviner, Choix);
		coups:=coups+1;
	end loop;
	New_Line;
	Put("Bravo. Vous avez trouvé ");
	Put(Nombre_A_Deviner, 1);
	Put(" en ");
	Put(coups, 1);
	Put(" Essais");


end Jeu_Devin_Exo1;
