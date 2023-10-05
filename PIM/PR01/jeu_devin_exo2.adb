with ada.Text_IO; use ada.Text_IO;
with ada.Integer_Text_IO; use ada.Integer_Text_IO;


procedure jeu_devin_exo2 is
	borneinff : Integer;
	bornesupp : Integer;
	proposition : Integer;
   reponse : Character;
   triche : Boolean;
   compteur : Integer;


begin
	bornesupp := 1000;
	borneinff := 1;
	proposition := 500;
   reponse := 'm';
   triche := False;
   compteur := 0;
   Put("Joue au jeu du devin, laisse moi deviner ton nombre");
   New_Line;

   while (reponse /= 't' or reponse /= 'T') and triche = false loop
      compteur := compteur+1;
    	Put("est ce que ");
    	Put(proposition, Width => 0);
    	Put(" est le bon nombre?");
      Get(reponse);


    	New_Line;


    	case reponse is
         when 'g'  | 'G' =>
            if proposition= bornesupp-1 then
               triche := True;
            else
               borneinff := proposition;
            end if;

         when 'p' | 'P' =>
            if proposition= borneinff then
               triche := True;
            else
               bornesupp := proposition;
            end if;

         when 't' | 'T' =>
            put("J'ai trouvé ton nombre je suis trop fort ! En seulement ");
            put(compteur,  Width => 0);
            put(" fois!!!");
            return ;
        	when others => null;
    	end case;

    	New_Line;
    	if (((bornesupp-borneinff) mod 2) = 0) then
        	proposition := borneinff+((bornesupp-borneinff)/2);

    	else
        	proposition := borneinff+(bornesupp-borneinff)/2;
    	end if;


	end loop;
   if triche = true then
      put("j'ai vu que tu as triché ! ce n'est pas bien !");
   end if;

end jeu_devin_exo2;



