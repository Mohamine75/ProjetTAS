type pterm = Var of string
           | App of pterm * pterm
           | Abs of string * pterm
           
let rec print_term (t : pterm) : string =
  match t with
    Var x -> x
  | App (t1, t2) -> "(" ^ (print_term t1) ^ " " ^ (print_term t2) ^ ")"
  | Abs (x, t) -> "(fun " ^ x ^ " -> " ^ (print_term t) ^ ")"

let compteur_var : int ref = ref 0

let nouvelle_var () : string = 
  compteur_var := !compteur_var + 1;
  "X" ^ (string_of_int !compteur_var)
  
let rec isValeur (t : pterm) : bool = 
  match t with
  | Var _ -> true
  | Abs (_, _) -> true
  | App(t1, t2) -> (match t1 with 
      | Var _ -> isValeur t2  (* x V est une valeur si t2 est aussi une valeur *)
      | _ -> false)
    
let rec alphaconv (t : pterm) : pterm =
  match t with
  | Var x -> Var x  (* Cas de base : renvoyer la variable telle quelle *)
  | App (t1, t2) -> App (alphaconv t1, alphaconv t2)  (* Appliquer alpha-conv sur les deux termes *)
  | Abs (x, t) -> 
      let x' = nouvelle_var () in  (* Créer une nouvelle variable *)
      let t' = alphaconv t in  (* Appliquer alpha-conv au corps de l'abstraction *)
      (* Renommer toutes les occurrences de x dans t' par x' *)
      match t' with
      | Abs (y, body) when y = x -> Abs (x', body)  (* Si y est la même variable, renommer *)
      | _ -> Abs (x', t')  (* Sinon, on renvoie simplement t' *)

      
(* Fonction de substitution améliorée avec alpha-conversion *)
let rec substitution (x : string) (v : pterm) (t : pterm) : pterm =
  match t with
  | Var y -> if y = x then v else t
  | App (t1, t2) -> App (substitution x v t1, substitution x v t2)
  | Abs (y, t1) ->
      if y = x then t  (* Ne pas substituer si c'est la même variable *)
      else 
        let v' = alphaconv v in (* Renomme v pour éviter les conflits *)
        Abs (y, substitution x v' t1)  (* Applique la substitution à t1 *)



let rec ltr_ctb_step (t : pterm) : pterm option =
  match t with
  | Var _ -> None  (* Pas de réduction pour une variable *)
  | Abs _ -> None  (* Pas de réduction pour une abstraction *)
  | App (Abs (x, t1), t2) -> 
      if isValeur t2 then 
        Some (substitution x t2 t1)  (* Appliquer la substitution si t2 est une valeur *)
      else 
        (match ltr_ctb_step t2 with  (* Sinon, essayer de réduire t2 *)
        | Some t2' -> Some (App (Abs (x, t1), t2'))  (* Appliquer la réduction à t2 *)
        | None -> None ) (* Si t2 ne peut pas être réduit *)
  | App (m, n) -> 
      match ltr_ctb_step m with  (* Essayer de réduire m d'abord *)
      | Some m' -> Some (App (m', n))  (* Réduire m et garder n *)
      | None -> match ltr_ctb_step n with  (* Sinon essayer de réduire n *)
                | Some n' -> Some (App (m, n'))  (* Réduire n *)
                | None -> None  (* Si m et n ne peuvent pas être réduits *)
        
            

let rec ltr_cbv_norm (t : pterm) : pterm =
  match (ltr_ctb_step t) with
  | Some reduc -> ltr_cbv_norm reduc
  | None -> t 

(* Définition des termes *)
let i = Abs("x", Var "x")
let k = Abs("x", Abs("y", Var "x"))
let s = Abs("x", Abs("y", Abs("z", App(App(Var "x", Var "z"), App(Var "y", Var "z")))))

(* Appliquons SKK *) 
let skk = App(App(s, k),k)
let ii = App(App(k,i),i)
let result = ltr_cbv_norm(skk)
(* Imprimer le résultat final *)
let () = print_endline (print_term result)
