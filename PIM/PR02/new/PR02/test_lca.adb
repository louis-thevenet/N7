with Ada.Text_IO;           use Ada.Text_IO;
with Ada.Integer_Text_IO;   use Ada.Integer_Text_IO;
with SDA_Exceptions; 		use SDA_Exceptions;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
	--! Les Unbounded_String ont une capacité variable, contrairement au String
	--! pour lesquelles une capacité doit être fixée.
with LCA;

procedure Test_LCA is

	package LCA_String_Integer is
		new LCA (T_Cle => Unbounded_String, T_Valeur => Integer);
	use LCA_String_Integer;


	-- Retourner une chaîne avec des guillemets autour de S
	function Avec_Guillemets (S: Unbounded_String) return String is
	begin
		return '"' & To_String (S) & '"';
	end;


	-- Utiliser & entre String à gauche et Unbounded_String à droite.  Des
	-- guillemets sont ajoutées autour de la Unbounded_String 
	-- Il s'agit d'un masquage de l'opérateur `&` défini dans Strings.Unbounded
	function "&" (Left: String; Right: Unbounded_String) return String is
	begin
		return Left & Avec_Guillemets (Right);
	end;


	-- Surcharge l'opérateur unaire "+" pour convertir une String
	-- en Unbounded_String.
	-- Cette astuce permet de simplifier l'initialisation
	-- de cles un peu plus loin.
	function "+" (Item : in String) return Unbounded_String
		renames To_Unbounded_String;


	-- Afficher une Unbounded_String et un entier.
	procedure Afficher (S : in Unbounded_String; N: in Integer) is
	begin
		Put (Avec_Guillemets (S));
		Put (" : ");
		Put (N, 1);
		New_Line;
	end Afficher;

	-- Afficher la Sda.
	procedure Afficher is
		new Pour_Chaque (Afficher);


	procedure Afficher_Avec_Guillemets (S : in Unbounded_String) is
	begin
		Put (Avec_Guillemets (S));
	end Afficher_Avec_Guillemets;

	procedure Afficher (N: in Integer) is 
	begin
		Put (N, 1);
	end;

	procedure Afficher_Interne is
		new Afficher_Debug(Afficher_Avec_Guillemets, Afficher);
	--

	Nb_Cles : constant Integer := 7;
	Cles : constant array (1..Nb_Cles) of Unbounded_String
			:= (+"un", +"deux", +"trois", +"quatre", +"cinq",
				+"quatre-vingt-dix-neuf", +"vingt-et-un");
	Inconnu : constant  Unbounded_String := To_Unbounded_String ("Inconnu");

	Donnees : constant array (1..Nb_Cles) of Integer
			:= (1, 2, 3, 4, 5, 99, 21);
	Somme_Donnees : constant Integer := 135;
	Somme_Donnees_Len4 : constant Integer := 7; -- somme si Length (Cle) = 4
	Somme_Donnees_Q: constant Integer := 103; -- somme si initiale de Cle = 'q'


	-- Initialiser l'annuaire avec les Donnees et Cles ci-dessus.
	-- Attention, c'est à l'appelant de libérer la mémoire associée en
	-- utilisant Detruire.
	-- Si Bavard est vrai, les insertions sont tracées (affichées).
	procedure Construire_Exemple_Sujet (Annuaire : out T_LCA; Bavard: Boolean := False) is
	begin
		Initialiser (Annuaire);
		pragma Assert (Est_Vide (Annuaire));
		pragma Assert (Taille (Annuaire) = 0);

		for I in 1..Nb_Cles loop
			Enregistrer (Annuaire, Cles (I), Donnees (I));

			if Bavard then
				Put_Line ("Après insertion de la clé " & Cles (I));
				Afficher (Annuaire);
				Afficher_Interne (Annuaire); New_Line;
				New_Line;
			else
				null;
			end if;

			pragma Assert (not Est_Vide (Annuaire));
			pragma Assert (Taille (Annuaire) = I);

			for J in 1..I loop
				pragma Assert (La_Valeur (Annuaire, Cles (J)) = Donnees (J));
			end loop;

			for J in I+1..Nb_Cles loop
				pragma Assert (not Cle_Presente (Annuaire, Cles (J)));
			end loop;

		end loop;
	end Construire_Exemple_Sujet;


	procedure Tester_Exemple_Sujet is
		Annuaire : T_LCA;
	begin
		Construire_Exemple_Sujet (Annuaire, True);
		Detruire (Annuaire);
	end Tester_Exemple_Sujet;


	-- Tester suppression en commençant par les derniers éléments ajoutés
	procedure Tester_Supprimer_Inverse is
		Annuaire : T_LCA;
	begin
		Put_Line ("=== Tester_Supprimer_Inverse..."); New_Line;

		Construire_Exemple_Sujet (Annuaire);

		for I in reverse 1..Nb_Cles loop

			Supprimer (Annuaire, Cles (I));

			Put_Line ("Après suppression de " & Cles (I) & " :");
			Afficher (Annuaire); New_Line;

			for J in 1..I-1 loop
				pragma Assert (Cle_Presente (Annuaire, Cles (J)));
				pragma Assert (La_Valeur (Annuaire, Cles (J)) = Donnees (J));
			end loop;

			for J in I..Nb_Cles loop
				pragma Assert (not Cle_Presente (Annuaire, Cles (J)));
			end loop;
		end loop;

		Detruire (Annuaire);
	end Tester_Supprimer_Inverse;


	-- Tester suppression en commençant les les premiers éléments ajoutés
	procedure Tester_Supprimer is
		Annuaire : T_LCA;
	begin
		Put_Line ("=== Tester_Supprimer..."); New_Line;

		Construire_Exemple_Sujet (Annuaire);

		for I in 1..Nb_Cles loop
			Put_Line ("Suppression de " & Cles (I) & " :");

			Supprimer (Annuaire, Cles (I));

			Afficher (Annuaire); New_Line;

			for J in 1..I loop
				pragma Assert (not Cle_Presente (Annuaire, Cles (J)));
			end loop;

			for J in I+1..Nb_Cles loop
				pragma Assert (Cle_Presente (Annuaire, Cles (J)));
				pragma Assert (La_Valeur (Annuaire, Cles (J)) = Donnees (J));
			end loop;
		end loop;

		Detruire (Annuaire);
	end Tester_Supprimer;


	procedure Tester_Supprimer_Un_Element is

		-- Tester supprimer sur un élément, celui à Indice dans Cles.
		procedure Tester_Supprimer_Un_Element (Indice: in Integer) is
			Annuaire : T_LCA;
		begin
			Construire_Exemple_Sujet (Annuaire);

			Put_Line ("Suppression de " & Cles (Indice) & " :");
			Supprimer (Annuaire, Cles (Indice));

			Afficher (Annuaire); New_Line;

			for J in 1..Nb_Cles loop
				if J = Indice then
					pragma Assert (not Cle_Presente (Annuaire, Cles (J)));
				else
					pragma Assert (Cle_Presente (Annuaire, Cles (J)));
				end if;
			end loop;

			Detruire (Annuaire);
		end Tester_Supprimer_Un_Element;

	begin
		Put_Line ("=== Tester_Supprimer_Un_Element..."); New_Line;

		for I in 1..Nb_Cles loop
			Tester_Supprimer_Un_Element (I);
		end loop;
	end Tester_Supprimer_Un_Element;


	procedure Tester_Remplacer_Un_Element is

		-- Tester enregistrer sur un élément présent, celui à Indice dans Cles.
		procedure Tester_Remplacer_Un_Element (Indice: in Integer; Nouveau: in Integer) is
			Annuaire : T_LCA;
		begin
			Construire_Exemple_Sujet (Annuaire);

			Put_Line ("Remplacement de " & Cles (Indice)
					& " par " & Integer'Image(Nouveau) & " :");
			enregistrer (Annuaire, Cles (Indice), Nouveau);

			Afficher (Annuaire); New_Line;

			for J in 1..Nb_Cles loop
				pragma Assert (Cle_Presente (Annuaire, Cles (J)));
				if J = Indice then
					pragma Assert (La_Valeur (Annuaire, Cles (J)) = Nouveau);
				else
					pragma Assert (La_Valeur (Annuaire, Cles (J)) = Donnees (J));
				end if;
			end loop;

			Detruire (Annuaire);
		end Tester_Remplacer_Un_Element;

	begin
		Put_Line ("=== Tester_Remplacer_Un_Element..."); New_Line;

		for I in 1..Nb_Cles loop
			Tester_Remplacer_Un_Element (I, 0);
			null;
		end loop;
	end Tester_Remplacer_Un_Element;


	procedure Tester_Supprimer_Erreur is
		Annuaire : T_LCA;
	begin
		begin
			Put_Line ("=== Tester_Supprimer_Erreur..."); New_Line;

			Construire_Exemple_Sujet (Annuaire);
			Supprimer (Annuaire, Inconnu);

		exception
			when Cle_Absente_Exception =>
				null;
			when others =>
				pragma Assert (False);
		end;
		Detruire (Annuaire);
	end Tester_Supprimer_Erreur;


	procedure Tester_La_Valeur_Erreur is
		Annuaire : T_LCA;
		Inutile: Integer;
	begin
		begin
			Put_Line ("=== Tester_La_Valeur_Erreur..."); New_Line;

			Construire_Exemple_Sujet (Annuaire);
			Inutile := La_Valeur (Annuaire, Inconnu);

		exception
			when Cle_Absente_Exception =>
				null;
			when others =>
				pragma Assert (False);
		end;
		Detruire (Annuaire);
	end Tester_La_Valeur_Erreur;


	procedure Tester_Pour_chaque is
		Annuaire : T_LCA;

		Somme: Integer;

		procedure Sommer (Cle: Unbounded_String; Valeur: Integer) is
		begin
			Put (" + ");
			Put (Valeur, 2);
			New_Line;

			Somme := Somme + Valeur;
		end;

		procedure Sommer is
			new Pour_Chaque (Sommer);

	begin
		Put_Line ("=== Tester_Pour_Chaque..."); New_Line;
		Construire_Exemple_Sujet(Annuaire);
		Somme := 0;
		Sommer (Annuaire);
		pragma Assert (Somme = Somme_Donnees);
		Detruire(Annuaire);
		New_Line;
	end Tester_Pour_chaque;


	procedure Tester_Pour_chaque_Somme_Si_Cle_Commence_Par_Q is
		Annuaire : T_LCA;

		Somme: Integer;

		procedure Sommer_Cle_Commence_Par_Q (Cle: Unbounded_String; Valeur: Integer) is
		begin
			if To_String (Cle) (1) = 'q' then
				Put (" + ");
				Put (Valeur, 2);
				New_Line;

				Somme := Somme + Valeur;
			else
				null;
			end if;
		end;

		procedure Sommer is
			new Pour_Chaque (Sommer_Cle_Commence_Par_Q);

	begin
		Put_Line ("=== Tester_Pour_Chaque_Somme_Si_Cle_Commence_Par_Q..."); New_Line;
		Construire_Exemple_Sujet(Annuaire);
		Somme := 0;
		Sommer (Annuaire);
		pragma Assert (Somme = Somme_Donnees_Q);
		Detruire(Annuaire);
		New_Line;
	end Tester_Pour_chaque_Somme_Si_Cle_Commence_Par_Q;



	procedure Tester_Pour_chaque_Somme_Len4_Avec_Exception is
		Annuaire : T_LCA;

		Somme: Integer;

		procedure Sommer_Len4_Avec_Exception (Cle: Unbounded_String; Valeur: Integer) is
			Nouvelle_Exception: Exception;
		begin
			if Length (Cle) = 4 then
				Put (" + ");
				Put (Valeur, 2);
				New_Line;

				Somme := Somme + Valeur;
			else
				raise Nouvelle_Exception;
			end if;
		end;

		procedure Sommer is
			new Pour_Chaque (Sommer_Len4_Avec_Exception);

	begin
		Put_Line ("=== Tester_Pour_Chaque_Somme_Len4_Avec_Exception..."); New_Line;
		Construire_Exemple_Sujet(Annuaire);
		Somme := 0;
		Sommer (Annuaire);
		pragma Assert (Somme = Somme_Donnees_Len4);
		Detruire(Annuaire);
		New_Line;
	end Tester_Pour_chaque_Somme_Len4_Avec_Exception;



begin
	Tester_Exemple_Sujet;
	Tester_Supprimer_Inverse;
	Tester_Supprimer;
	Tester_Supprimer_Un_Element;
	Tester_Remplacer_Un_Element;
	Tester_Supprimer_Erreur;
	Tester_La_Valeur_Erreur;
	Tester_Pour_chaque;
	Tester_Pour_chaque_Somme_Si_Cle_Commence_Par_Q;
	Tester_Pour_chaque_Somme_Len4_Avec_Exception;
	Put_Line ("Fin des tests : OK.");
end Test_LCA;
