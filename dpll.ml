open List

(* fonctions utilitaires *********************************************)
(* filter_map : ('a -> 'b option) -> 'a list -> 'b list
   disponible depuis la version 4.08.0 de OCaml dans le module List :
   pour chaque élément de `list', appliquer `filter' :
   - si le résultat est `Some e', ajouter `e' au résultat ;
   - si le résultat est `None', ne rien ajouter au résultat.
   Attention, cette implémentation inverse l'ordre de la liste *)
let filter_map filter list =
  let rec aux list ret =
    match list with
    | []   -> ret
    | h::t -> match (filter h) with
      | None   -> aux t ret
      | Some e -> aux t (e::ret)
  in aux list []

(* print_modele : int list option -> unit
   affichage du résultat *)
let print_modele: int list option -> unit = function
  | None   -> print_string "UNSAT\n"
  | Some modele -> print_string "SAT\n";
     let modele2 = sort (fun i j -> (abs i) - (abs j)) modele in
     List.iter (fun i -> print_int i; print_string " ") modele2;
     print_string "0\n"

(* ensembles de clauses de test *)
let exemple_3_12 = [[1;2;-3];[2;3];[-1;-2;3];[-1;-3];[1;-2]]
let exemple_7_2 = [[1;-1;-3];[-2;3];[-2]]
let exemple_7_4 = [[1;2;3];[-1;2;3];[3];[1;-2;-3];[-1;-2;-3];[-3]]
let exemple_7_8 = [[1;-2;3];[1;-3];[2;3];[1;-2]]
let systeme = [[-1;2];[1;-2];[1;-3];[1;2;3];[-1;-2]]
let dependances = [[1];[-1;2];[-1;3;4;5];[-2;6];[-3;7];[-4;8;9];[-5;9];[-9;-6];[-9;-7];[-4;-5];[-8;-9];[-6;-7]]
let coloriage = [[1;2;3];[4;5;6];[7;8;9];[10;11;12];[13;14;15];[16;17;18];[19;20;21];[-1;-2];[-1;-3];[-2;-3];[-4;-5];[-4;-6];[-5;-6];[-7;-8];[-7;-9];[-8;-9];[-10;-11];[-10;-12];[-11;-12];[-13;-14];[-13;-15];[-14;-15];[-16;-17];[-16;-18];[-17;-18];[-19;-20];[-19;-21];[-20;-21];[-1;-4];[-2;-5];[-3;-6];[-1;-7];[-2;-8];[-3;-9];[-4;-7];[-5;-8];[-6;-9];[-4;-10];[-5;-11];[-6;-12];[-7;-10];[-8;-11];[-9;-12];[-7;-13];[-8;-14];[-9;-15];[-7;-16];[-8;-17];[-9;-18];[-10;-13];[-11;-14];[-12;-15];[-13;-16];[-14;-17];[-15;-18]]

(********************************************************************)

(* simplifie : int -> int list list -> int list list 
   applique la simplification de l'ensemble des clauses en mettant
   le littéral i à vrai *)
let rec simplifie i clauses =
  match clauses with 
  |[]->[[]] (*Si liste vide Alors retourner int list list [[]]*)
  (*Si la formule consiste en une seule clause Alors si i appartient à celle-ci , retourner [] sinon si le dual de i appartient à la clause on filtre la liste l et on enlève (-i) *)
  |[l]-> if List.exists (fun x-> x=i) l then [] else if List.exists (fun x-> x=(-i)) l then [List.filter (fun x -> x<>(-i)) l ] else [l]
  (*Si la formule à plusieurs clause on vérifie ce qui précède sur la première clause et on appelle récursivement la fonction sur le reste des clauses  *)
  |l::l'->
  if List.exists (fun x->x=i) l then 
  simplifie i l' 
  else if List.exists (fun x-> x=(-i)) l then 
  (filter (fun x -> x<>(-i)) l )::simplifie i l' 
  else l::simplifie i l';;
  
(*Tests de la fonction simplifie*)
simplifie 1 exemple_3_12;;
simplifie 2 exemple_3_12;;
simplifie 3 exemple_3_12;;
simplifie 2 (simplifie 1 coloriage) ;;
(*soit Interprétation I=[1,2,-3,4,-5,6,-7,8,-9] un modèle pour dependance , donc si on simplifie dependance selon cette intérpretation on aboutira à un ensemble vide*)
simplifie 1(simplifie 2 (simplifie (-3) (simplifie 4 (simplifie (-5) (simplifie 6 (simplifie (-7) (simplifie 8 (simplifie (-9) dependances)))))))) (*c'est le cas*)


(* solveur_split : int list list -> int list -> int list option
   exemple d'utilisation de `simplifie' *)
let rec solveur_split clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Some interpretation else
  (* un clause vide est insatisfiable *)
  if mem [] clauses then None else
  (* branchement *) 
  let l = hd (hd clauses) in
  let branche = solveur_split (simplifie l clauses) (l::interpretation) in
  match branche with
  | None -> solveur_split (simplifie (-l) clauses) ((-l)::interpretation)
  | _    -> branche

(* tests *)
let () = print_modele (solveur_split systeme []) 
let () = print_modele (solveur_split dependances []) 
let () = print_modele (solveur_split coloriage []) 

(* solveur dpll récursif *)
    
(* unitaire : int list list -> int
    - si `clauses' contient au moins une clause unitaire, retourne
      le littéral de cette clause unitaire ;
    - sinon, lève une exception `Not_found' *)
(*Dans la fonction unitaire on a définie le numéro 0 comme étant le résultat s'il n'existe pas de clause unitaire*)
let rec unitaire clauses =
  match clauses with 
  |[]-> 0(*failwith("Not_Found")*) (*Cas où il n'existe pas de clause unitaire*)
  |[l] when (List.length l = 1) -> List.nth l 0 (*Si la formule consiste en une seule clause qui est composée d'un seul littéral Alors c'est une clause unitaire , on retoune cette clause *)
  |l::l'-> if List.length l = 1 then List.nth l 0 else unitaire l' ;; (*On teste si l est unitaire sinon on appelle la fonction récursivement pour en trouver des clauses unitaires (au moins une) *)
  
(*Tests de la fonction unitaire*)
unitaire dependances;;
unitaire exemple_7_2;;
unitaire coloriage;; (*Cette instruction retourne un 0 , car il n'existe pas de clauses unitaire dans coloriage*)
unitaire exemple_3_12;;
unitaire exemple_7_4;;
unitaire exemple_7_8;;


(* pur : int list list -> int
    - si `clauses' contient au moins un littéral pur, retourne
      ce littéral ;
    - sinon, lève une exception `Failure "pas de littéral pur"' *)
let pur clauses =
  (*Définition d'une fonction récursive localement qui consiste en un remplissage d'un accumulateur qui va servir comme liste d'élimination de littéraux qui co-existent avec leurs duaux*)
  let rec determiner acc l=                                
    match l with                                     
    | [] -> 0 (*failwith "pas de littéral pur"  *) (*Cas où il n'existe pas de littéral pur*)
    | x::l'->      
        (*on teste si x ou (-x) n'est pas présent dans l'accumulateur et si son dual n'existe pas dans la suite des clauses donc x est pur sinon on appelle récursivement ajouter pour en trouver au moins un littéral pur *)
        if  not( List.mem (x) acc || List.mem (-x) acc) && not(List.mem (-x) l') then x                             
        else determiner (x::acc) l'                             
  in 
  determiner [] (List.concat clauses) ;; (*on appelle la fonction determiner sur List.concat clauses == List.flatten clauses qui supprime un niveau de liste dans clauses i.e. int list list => int list  *)
  
(*Tests de la fonction pur*)
pur exemple_7_2;;
pur coloriage;;
pur exemple_3_12;;
pur exemple_7_4;;
pur exemple_7_8;;

(* solveur_dpll_rec : int list list -> int list -> int list option *)
let rec solveur_dpll_rec clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Some interpretation else
  (* un clause vide est insatisfiable *)
  if mem [] clauses then None else
  (*on cherche une clause unitaire et on appelle récursivement solveur_dpll_rec sur l'ensemble simplifié de clauses selon cet clause unitaire et on la met dans l'accumulateur pour construire le modèle*)
  let c_unitaire= unitaire clauses in 
  if c_unitaire != 0 then solveur_dpll_rec (simplifie c_unitaire clauses) (c_unitaire::interpretation) else 
  (*Sinon on cherche un littéral pur et on appelle récursivement solveur_dpll_rec sur l'ensemble simplifié de clauses selon ce littéral et on le met dans l'accumulateur pour construire le modèle*)
  let l_pur= pur clauses in
  if l_pur != 0 then solveur_dpll_rec (simplifie l_pur clauses) (l_pur::interpretation) else 
  (*Sinon on prend un littéral arbitraire de l'ensmble de littéraux constituant la formule et on applique la récursivité sur l'ensemble simplifié avec le littéral et son dual -en deux appelles- *)
  let choix_lit = List.nth (List.flatten clauses) (Random.int (List.length (List.flatten clauses))) in
  let branche = solveur_dpll_rec (simplifie choix_lit clauses) (choix_lit::interpretation) in
  match branche with 
  |None -> solveur_dpll_rec (simplifie (-choix_lit) clauses) ((-choix_lit)::interpretation)
  | _ -> branche 

(* tests *)
 let () = print_modele (solveur_dpll_rec systeme []) 
 let () = print_modele (solveur_dpll_rec dependances []) 
 let () = print_modele (solveur_dpll_rec coloriage []) 

let () =
  let clauses = Dimacs.parse Sys.argv.(1) in
  print_modele (solveur_dpll_rec clauses [])
