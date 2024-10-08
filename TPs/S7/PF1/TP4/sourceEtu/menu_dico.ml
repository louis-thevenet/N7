let affiche_menu () =
  let () = print_string "\n 0 - Quitter\n" in
  let () = print_string " 1 - Chercher un mot\n" in
  let () = print_string " 2 - Ajouter un mot\n" in
  let () = print_string " 3 - Retirer un mot\n" in
  print_string " 4 - Afficher le dictionnaire\n\n> "

let gere_dico fd fr lm em nouveau appartient ajout retrait affiche mots =
  let rec mainloop dico fin =
    if fin then () else
      let () = affiche_menu () in
      let commande = read_line () in
      let dico, fin = match commande with
        | "0" -> dico, true;
        | "1" ->
           let () = print_string "\nEntrer le mot à rechercher :\n" in
           let mot = lm () in
           let () = print_newline () in
           let () = print_string " -> " in
           let () = em mot in
           let () =
             if appartient mot dico then print_string " présent\n\n"
             else print_string " non présent\n\n" in
           dico, false
        | "2" ->
           let () = print_string "\nEntrer le mot à ajouter :\n" in
           let mot = lm () in
           let dico = ajout mot dico in
           let () = print_newline () in
           let () = print_string " -> " in
           let () = em mot in
           let () = print_string " ajouté\n\n" in
           dico, false
        | "3" ->
           let () = print_string "\nEntrer le mot à retirer :\n" in
           let mot = lm () in
           let dico = retrait mot dico in
           let () = print_newline () in
           let () = print_string " <- " in
           let () = em mot in
           let () = print_string " retiré\n\n" in
           dico, false
        | "4" ->
           let () = print_string "\n------------------------------\n\n" in
           let () = affiche em dico in
           let () = print_string "\n------------------------------\n\n" in
           dico, false
        | _   ->
           let () = print_string "\n\n**** Erreur de Saisie ****\n\n" in
           dico, false in
      mainloop dico fin in
  let dico = List.fold_right ajout mots (nouveau fd fr) in
  mainloop dico false
