with Text_Io;              use Text_Io;
with Ada.Integer_Text_Io;  use Ada.Integer_Text_Io;
with Alea;

-- Auteur : Louis THEVENET

procedure Jeu_Devin_Exo1 is
	-- Jouer au jeu du devin en faisant deviner le nombre à l'utilisateur

	package Mon_Alea is new Alea (1, 999);
	use Mon_Alea;

	Nombre_A_Deviner, Coups, Choix: Integer;
	Fini: Boolean;

begin
	Get_Random_Number(Nombre_A_Deviner);
	Put ("J'ai choisi un nombre entre 1 et 999.");

	-- Faire deviner le nombre
	Coups := 1;
	Fini := false;
	while not Fini loop
		-- Obtenir le choix de l'utilsateur
		New_Line;
		Put ("Proposition ");
		Put (coups, 1);
		Put(" : ");
		Get (Choix);

		-- Traiter choix
		if Nombre_A_Deviner = Choix then
			Put("Trouvé");
			Fini := true;
		elsif Nombre_A_Deviner < Choix then
			Put ("Trop grand.");
			Fini := false;
		else 
			Put("Trop petit.");
			Fini:= false;
		end if;
		coups:=coups+1;
	end loop;
	New_Line;
	Put("Bravo. Vous avez trouvé ");
	Put(Nombre_A_Deviner, 1);
	Put(" en ");
	Put(coups, 1);
	Put(" essais");
	New_Line;

end Jeu_Devin_Exo1;
