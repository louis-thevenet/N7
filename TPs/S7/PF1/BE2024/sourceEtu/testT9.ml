open Intuitive
open Encodage
open StructureDonnees

module IntuitiveT9S (S : StructureDonnees) = struct
  module IntuitiveT9 = Intuitive (T9) (S)

  (* Tests de encoder_lettre *)
  let%test _ = IntuitiveT9.encoder_lettre 'a' = 2
  let%test _ = IntuitiveT9.encoder_lettre 'b' = 2
  let%test _ = IntuitiveT9.encoder_lettre 'c' = 2
  let%test _ = IntuitiveT9.encoder_lettre 'd' = 3
  let%test _ = IntuitiveT9.encoder_lettre 'e' = 3
  let%test _ = IntuitiveT9.encoder_lettre 'f' = 3
  let%test _ = IntuitiveT9.encoder_lettre 'g' = 4
  let%test _ = IntuitiveT9.encoder_lettre 'h' = 4
  let%test _ = IntuitiveT9.encoder_lettre 'i' = 4
  let%test _ = IntuitiveT9.encoder_lettre 'j' = 5
  let%test _ = IntuitiveT9.encoder_lettre 'k' = 5
  let%test _ = IntuitiveT9.encoder_lettre 'l' = 5
  let%test _ = IntuitiveT9.encoder_lettre 'm' = 6
  let%test _ = IntuitiveT9.encoder_lettre 'n' = 6
  let%test _ = IntuitiveT9.encoder_lettre 'o' = 6
  let%test _ = IntuitiveT9.encoder_lettre 'p' = 7
  let%test _ = IntuitiveT9.encoder_lettre 'q' = 7
  let%test _ = IntuitiveT9.encoder_lettre 'r' = 7
  let%test _ = IntuitiveT9.encoder_lettre 's' = 7
  let%test _ = IntuitiveT9.encoder_lettre 't' = 8
  let%test _ = IntuitiveT9.encoder_lettre 'u' = 8
  let%test _ = IntuitiveT9.encoder_lettre 'v' = 8
  let%test _ = IntuitiveT9.encoder_lettre 'w' = 9
  let%test _ = IntuitiveT9.encoder_lettre 'x' = 9
  let%test _ = IntuitiveT9.encoder_lettre 'y' = 9
  let%test _ = IntuitiveT9.encoder_lettre 'z' = 9
  let%test _ = IntuitiveT9.encoder_lettre '&' = 0

  (* Tests de encoder_mot *)
  let%test _ = IntuitiveT9.encoder_mot "" = []
  let%test _ = IntuitiveT9.encoder_mot "a" = [ 2 ]
  let%test _ = IntuitiveT9.encoder_mot "bonjour" = [ 2; 6; 6; 5; 6; 8; 7 ]
  let%test _ = IntuitiveT9.encoder_mot "bonjour!" = [ 2; 6; 6; 5; 6; 8; 7; 0 ]
  let%test _ = IntuitiveT9.encoder_mot "ocaml" = [ 6; 2; 2; 6; 5 ]
  let dico_fr = IntuitiveT9.creer_dico "dico_fr.txt"

  (* Tests de décoder mot *)
  let%test _ = IntuitiveT9.decoder_mot [ 5; 4; 6 ] S.empty = []

  let%test _ =
    IntuitiveT9.decoder_mot [ 2; 6; 6; 5; 6; 8; 7 ] dico_fr = [ "bonjour" ]

  let%test _ =
    IntuitiveT9.decoder_mot [ 8; 3; 6; 3; 7; 3 ] dico_fr
    = [ "venere"; "vendre"; "tendre" ]

  let%test _ =
    IntuitiveT9.decoder_mot [ 2; 6; 3 ] dico_fr
    = [ "cod"; "cnd"; "bof"; "aof"; "ane"; "ame" ]

  let%test _ = IntuitiveT9.decoder_mot [ 8; 3; 7; 3; 6; 3 ] dico_fr = []

  let%test _ =
    IntuitiveT9.decoder_mot [ 2; 8; 7; 3; 5; 4; 3 ] dico_fr = [ "aurelie" ]

  (* Tests de max_mots_code_identique *)
  let%test _ = IntuitiveT9.max_mots_code_identique S.empty = 0
  let%test _ = IntuitiveT9.max_mots_code_identique dico_fr = 8

  (* Tests de prefixe *)
  let%test _ =
    List.sort String.compare (IntuitiveT9.prefixe [ 3; 8 ] S.empty) = []

  let%test _ =
    List.sort String.compare (IntuitiveT9.prefixe [ 9; 2; 3 ] dico_fr)
    = [ "wading"; "zad" ]

  let%test _ =
    List.sort String.compare (IntuitiveT9.prefixe [ 2; 6; 6; 5; 6 ] dico_fr)
    = [
        "bonjour";
        "bookmaker";
        "conjoint";
        "conjointe";
        "conjointement";
        "conjoncteur";
        "conjoncteurdisjoncteur";
        "conjoncteursdisjoncteurs";
        "conjonctif";
        "conjonction";
        "conjonctival";
        "conjonctivaux";
        "conjonctive";
        "conjonctivite";
        "conjoncture";
        "conjoncturel";
        "conjoncturelle";
        "conjoncturiste";
      ]

  let%test _ =
    List.sort String.compare (IntuitiveT9.prefixe [ 2; 2; 2; 2; 2 ] dico_fr)
    = [
        "abaca";
        "accablant";
        "accable";
        "accablement";
        "accabler";
        "babacool";
        "babbage";
        "baccalaureat";
        "baccara";
        "baccarat";
        "cacabant";
        "cacabe";
        "cacaber";
      ]

  let%test _ = List.sort String.compare (IntuitiveT9.prefixe [] S.empty) = []
end

module IntuitiveT9Assoc = IntuitiveT9S (ListAssoc)
module IntuitiveT9Arbre = IntuitiveT9S (Arbre)
