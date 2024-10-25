open Encodage
open Chaines
open StructureDonnees

module Intuitive (E : Encodage) (S : StructureDonnees) = struct
  (************)
  (* Encodage *)
  (************)

  (* encoder_lettre : char -> int *)
  (* Encode une lettre, c'est-à-dire indique la touche qu'il faut
     appuyer pour saisir la lettre *)
  (* Le paramètre est la lettre à encoder *)
  (* Renvoie la touche à utiliser si c'est une lettre minuscule,
     0 pour les autres caractères *)
  let encoder_lettre lettre =
    let codes =
      List.filter_map
        (fun (n, lettres) -> if List.mem lettre lettres then Some n else None)
        E.map
    in
    if List.length codes = 0 then 0 else List.hd codes

  (* encoder_mot : string -> int list *)
  (* Encode un mot, c'est-à-dire indique la suite de touches à appuyer
     pour saisir le mot *)
  (* Le paramètre est le mot à encoder *)
  (* Renvoie la liste des touches à composer *)

  let encoder_mot mot =
    if String.empty = mot then []
    else List.map (fun c -> encoder_lettre c) (List.of_seq (String.to_seq mot))

  (***************************************************************************)
  (* Décodage                                                                *)
  (* Nécessite un dictionnaire car un même code est associé à plusieurs mots *)
  (***************************************************************************)

  (* ajouter : dico -> string -> dico *)
  (* Ajoute un mot à un dictionnaire *)
  (* Le premier paramètre est le dictionnaire dans lequel le mot doit
     être ajouté *)
  (* Le second paramètre est le mot à ajouter *)
  (* Renvoie le nouveau dictionnaire *)
  let ajouter dico mot = S.ajouter (encoder_mot mot) mot dico

  (* decoder_mot -> dico -> int list -> string list *)
  (* Identifie l'ensemble des mots potentiellement saisis à partir d'une suite de touches  *)
  (* Le premier paramètre est la liste des touches appuyées *)
  (* Le second paramètre est le dictionnaire *)
  (* Renvoie l'ensemble des mots du dictionnaire correspondants aux touches appuyées *)

  let decoder_mot encodage dico = S.chercher encodage dico

  (* Pour les tests combinés de ajoute et decoder_mot *)
  (* Doivent passer, car ne dépendent pas de l'ordre dans les listes *)

  let creer_dico file =
    let channel = open_in file in
    try
      let rec read_lines acc =
        try
          let line = input_line channel in
          read_lines (ajouter acc line)
        with End_of_file -> acc
      in
      let lines = read_lines S.empty in
      close_in channel;
      lines
    with e ->
      close_in channel;
      raise e

  (* max_mots_code_identique : dico -> int *)
  (* Calcule le nombre maximum de mots associés à un même code dans un
     dictionnaire *)
  let max_mots_code_identique dico = S.max_mots_code_identique dico

  (* prefixe : int list -> dico -> string list *)
  (* Liste tous les mots dont le préfix est la liste de touches passée en paramètre *)
  (* Lorsque le prefixe est vide, liste l'ensemble des mots du dictionnaire *)
  let prefixe encodage dico = S.prefixe encodage dico
end
