type pterm = Var of string
           | App of pterm * pterm
           | Abs of string * pterm
                    
let rec print_term (t : pterm) : string =
  match t with
    Var x -> x
  | App (t1 , t2) -> "(" ^ ( print_term t1) ^" "^ ( print_term t2) ^ ")"
  | Abs (x, t) -> "(fun " ^ x ^" -> " ^ ( print_term t) ^")"
                  
                  
let compteur_var : int ref = ref 0
    
let nouvelle_var () : string = compteur_var := ! compteur_var + 1;
  "X"^( string_of_int ! compteur_var )
    
    

let rec substitution (x : string) (v : pterm) (t : pterm) : pterm =
  match t with
  | Var y -> if y = x then v else Var y
  | App (t1, t2) -> App (substitution x v t1, substitution x v t2)
  | Abs (y, t1) -> if y = x then Abs (y, t1) else Abs (y, substitution x v t1)


let rec alphaconv (t : pterm) : pterm =
  match t with
  | Var x -> Var x
  | App (t1, t2) -> App (alphaconv t1, alphaconv t2)
  | Abs (x, t) ->
      let new_var = nouvelle_var () in
      let t' = substitution x (Var new_var) t in
      Abs (new_var, alphaconv t')

      

let rec isValeur (t:pterm) : bool = 
  match t with
  |Var _ -> true
  |Abs (_, _) -> true
  |App(t1,t2) -> match t1 with
    |Var _ -> true && (isValeur t2)
    |_ -> false


let rec ltr_ctb_step (t : pterm) : pterm option =
  match t with
  | Var _ -> None
  | Abs (_, _) -> None
  | App(t1, t2) -> match t1 with 
    | Abs(x, t') when isValeur t2 -> Some (substitution x t' t2)  (* Applique la réduction si t2 est une valeur *)
    | App(_, _) -> 
      let tmp = ltr_ctb_step t1 in 
      (match tmp with 
      | Some t1' -> Some (App(t1', t2))  (* Réduit t1 si possible *)
      | None -> ltr_ctb_step t2)  (* Si t1 ne se réduit pas, essaie de réduire t2 *)
    | _ -> None
    

let rec ltr_cbv_norm (t : pterm) : pterm =
match (ltr_ctb_step t) with
|Some reduc -> ltr_cbv_norm reduc
|None -> t 


(* Identité : fun x -> x appliqué à un argument *)
let id = Abs("x", Var "x")
let term = App(id, Var "y")

(* Réduction attendue : l'application de la fonction identité à y renvoie y *)
let result = ltr_cbv_norm term;;  (* Résultat attendu : Var "y" *)

(* Composition de deux fonctions identitaires : (fun x -> x) (fun y -> y) *)
let id1 = Abs("x", Var "x")
let id2 = Abs("y", Var "y")
let term = App(id1, id2)

(* Réduction attendue : la fonction identité renvoie la deuxième identité *)
let result = ltr_cbv_norm term  (* Résultat attendu : Abs("y", Var "y") *)

(* Application : (fun x -> x) ((fun z -> z) (Var "w")) *)
let inner_abs = Abs("z", Var "z")
let id = Abs("x", Var "x")
let term = App(id, App(inner_abs, Var "w"))

(* Réduction attendue : réduire d'abord (fun z -> z) (Var "w"), ce qui donne Var "w", puis appliquer la fonction identité *)
let result = ltr_cbv_norm term  (* Résultat attendu : Var "w" *)
(* Une fonction appliquée à une application non réductible *)
let f = Abs("x", Var "x")
let term = App(f, App(Var "y", Var "z"))  (* (fun x -> x) (y z) *)

(* Réduction attendue : ne peut pas se réduire car (y z) n'est pas une valeur *)
let result = ltr_cbv_norm term  (* Résultat attendu : App(f, App(Var "y", Var "z")) *)
