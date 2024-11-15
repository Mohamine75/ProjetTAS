exception Timeout_exception 
let global_timeout = 1.0  
let compteur_var : int ref = ref 0
type pterm =
    | Var of string
    | App of pterm * pterm
    | Abs of string * pterm
    | Int of int  (* Pour les entiers *)
    | Add of pterm * pterm  (* Addition *)
    | Sub of pterm * pterm  (* Soustraction *)
    | IfZero of pterm * pterm * pterm  (* If zero then else *)
    | EmptyList  (* Représente une liste vide *)
    | Cons of pterm * pterm  (* Construit une liste *)
    | IfEmpty of pterm * pterm * pterm  (* If empty then else *)
    | Fix of string * pterm  (* Point fixe *)
    | Let of string * pterm * pterm  (* Let-in *)
let nouvelle_var () : string = 
  compteur_var := !compteur_var + 1;
  "X" ^ (string_of_int !compteur_var)
type ptype = Varp of string | Arr of ptype * ptype | Nat
let rec print_term (t : pterm) : string =
  match t with
  | Var x -> x
  | App (t1, t2) -> "(" ^ (print_term t1) ^ " " ^ (print_term t2) ^ ")"
  | Abs (x, t) -> "(fun " ^ x ^ " -> " ^ (print_term t) ^ ")"
  | Int n -> string_of_int n
  | Add (t1, t2) -> "(" ^ (print_term t1) ^ " + " ^ (print_term t2) ^ ")"
  | Sub (t1, t2) -> "(" ^ (print_term t1) ^ " - " ^ (print_term t2) ^ ")"
  | IfZero (t1, t2, t3) -> "(ifzero " ^ (print_term t1) ^ " then " ^ (print_term t2) ^ " else " ^ (print_term t3) ^ ")"
  | EmptyList -> "[]"
  | Cons (head, tail) -> "(cons " ^ (print_term head) ^ " " ^ (print_term tail) ^ ")"
  | IfEmpty (t1, t2, t3) -> "(ifempty " ^ (print_term t1) ^ " then " ^ (print_term t2) ^ " else " ^ (print_term t3) ^ ")"
  | Fix (x, t) -> "(fix " ^ x ^ " -> " ^ (print_term t) ^ ")"
  | Let (x, t1, t2) -> "(let " ^ x ^ " = " ^ (print_term t1) ^ " in " ^ (print_term t2) ^ ")"
let compteur_var_t : int ref = ref 0
let nouvelle_var_t () : string = compteur_var := !compteur_var + 1;
  "T"^( string_of_int ! compteur_var )
type equa = (ptype * ptype) list
type env = (string * ptype) list
let rec cherche_type (v : string) (e : env) : ptype =
  match e with
  |(s,t)::reste -> if v=s then t else cherche_type v reste 
  |_ -> Nat
  let rec genere_equa (te : pterm) (ty : ptype) (e : env) : equa =
    match te with
    | Var v -> 
        let t_var = cherche_type v e in
        [(t_var, ty)]  (* Générer l'équation t_var = ty *)
    
    | Abs (x, t) -> 
        let ta = Varp (nouvelle_var_t ()) in  (* Type pour l'argument de la fonction *)
        let tr = Varp (nouvelle_var_t ()) in  (* Type pour le résultat de la fonction *)
        let e' = (x, ta) :: e in  (* Ajouter le paramètre à l'environnement avec son type *)
        let equa_body = genere_equa t tr e' in  (* Générer les équations pour le corps de la fonction *)
        (ty, Arr (ta, tr)) :: equa_body  (* L'abs a le type Arr (ta, tr) *)
    
    | App (t1, t2) -> 
        let ta = Varp (nouvelle_var_t ()) in  (* Type pour l'argument de t1 *)
        let tr = Varp (nouvelle_var_t ()) in  (* Type pour le résultat de t1 *)
        
        (* t1 doit être une fonction, donc son type est Arr (ta, tr) *)
        let equa_t1 = genere_equa t1 (Arr (ta, tr)) e in  (* Générer les équations pour t1 de type fonction *)
        
        (* t2 doit être de type ta, c'est-à-dire le type attendu pour l'argument de la fonction *)
        let equa_t2 = genere_equa t2 ta e in  (* Générer les équations pour t2, l'argument de la fonction *)
        
        (* Combiner les équations générées pour t1 et t2 *)
        equa_t1 @ equa_t2

let rec occur_check (s:string) (ty:ptype) : bool  = 
  match ty with
  | Arr (t1,t2) -> (occur_check s t1) || (occur_check s t2)
  | Varp x -> if x=s then true else false
  | _ -> false

let rec substitution_type (s : string) (t_sub : ptype) (ty : ptype) : ptype =
  match ty with
  | Varp x -> if x = s then t_sub else Varp x  (* Remplace si c'est la variable à substituer *)
  | Arr (t1, t2) -> Arr (substitution_type s t_sub t1, substitution_type s t_sub t2)  (* Applique récursivement aux sous-types *)
  | Nat -> Nat  (* Aucun changement pour Nat *)

  let rec substitution_systeme (s : string) (t_sub : ptype) (systeme : (ptype * ptype) list) : (ptype * ptype) list =
    List.map (fun (t1, t2) -> 
        (substitution_type s t_sub t1, substitution_type s t_sub t2)
      ) systeme
  
let rec egalite_type (t1 : ptype) ( t2 :ptype) : bool = 
  match t1,t2 with
  |Varp s1, Varp s2 -> s1 = s2
  |(Arr (t11,t12)),(Arr(t21,t22)) -> (egalite_type t11 t21) && (egalite_type t12  t22)
  | Nat,Nat -> true 
  | _,_ -> false
 
  let rec uni_step (eq : (ptype * ptype) list) : (ptype * ptype) list =
    match eq with
    | [] -> []  (* Cas d'arrêt : plus d'équations *)
    | (t1, t2) :: queue ->
        if egalite_type t1 t2 then
          (* Si les types sont égaux, on les supprime de la liste *)
          uni_step queue
        else
          match (t1, t2) with
          | Varp s, _ ->
              if occur_check s t2 then
                failwith "Unification échoue : occur check"
              else
                let substituted_eqs = substitution_systeme s t2 queue in
                (t1, t2) :: uni_step substituted_eqs  (* Applique les substitutions et continue *)
    
          | _, Varp s ->
              if occur_check s t1 then
                failwith "Unification échoue : occur check"
              else
                let substituted_eqs = substitution_systeme s t1 queue in
                (t1, t2) :: uni_step substituted_eqs  (* Applique les substitutions et continue *)
    
          | Arr (t1a, t1b), Arr (t2a, t2b) ->
              (* Les types sont des flèches, on les décompose en sous-types *)
              let new_eqs = (t1a, t2a) :: (t1b, t2b) :: queue in
              uni_step new_eqs
    
          | Nat, Nat -> uni_step queue  (* Les types sont égaux (Nat), on les supprime de la liste *)
    
          | _ -> failwith "Unification échoue : types incompatibles"
    
          let rec resoudre_systeme eq (substitutions_acc : (string * ptype) list) (max_iter : int) : ((ptype * ptype) list * (string * ptype) list) option =
            if max_iter <= 0 then
              None  (* Limite de récursion pour éviter les boucles infinies *)
          
            else match eq with
            | [] -> Some ([], substitutions_acc)  (* Si aucune équation, retourner l'état actuel *)
          
            | _ ->
                try
                  let next_eqs = uni_step eq in
                  Printf.printf "[DEBUG] Current equations: %s\n" (List.fold_left (fun acc (t1, t2) -> acc ^ print_type t1 ^ " = " ^ print_type t2 ^ ", ") "" next_eqs);
          
                  (* Si les équations ne changent pas entre les itérations, on peut arrêter l'unification *)
                  if next_eqs = eq then
                    Some (next_eqs, substitutions_acc)
                  else
                    let substituted_eqs = List.map (fun (t1, t2) ->
                      (* Substitution appliquée seulement si t1 et t2 ont évolué *)
                      (List.fold_left (fun acc (s, t_sub) -> substitution_type s t_sub acc) t1 substitutions_acc,
                        List.fold_left (fun acc (s, t_sub) -> substitution_type s t_sub acc) t2 substitutions_acc)
                    ) next_eqs in
                    resoudre_systeme substituted_eqs substitutions_acc (max_iter - 1)
                with Failure _ -> None  (* Si l'unification échoue, on retourne None *)
                        
let infere_type (terme : pterm) (env : env) : ptype option =
  (* Générer une nouvelle variable de type pour le terme *)
  let nouveau_type = Varp "T" in
  (* Générer les équations *)
  let equa = genere_equa terme nouveau_type env in
  (* Essayer de résoudre les équations avec le timeout global *)
  match resoudre_systeme equa with
  | Some _ -> Some nouveau_type  (* Si le système est résolu, le terme est typé *)
  | None -> None  (* Sinon, le terme n'est pas typable *)  
                 
(* Mise à jour de la fonction `isValeur` pour les nouvelles fonctionnalités *)
let rec isValeur (t : pterm) : bool = 
  match t with
  | Var _ -> true
  | Abs (_, _) -> true
  | Int _ -> true  (* Les entiers sont des valeurs *)
  | EmptyList -> true  (* Liste vide est une valeur *)
  | Cons (head, tail) -> isValeur head && isValeur tail  (* Liste construite est valeur si ses éléments sont des valeurs *)
  | _ -> false  (* Autres cas ne sont pas considérés comme valeurs *)
let rec substitution (x : string) (v : pterm) (t : pterm) : pterm =
  match t with
  | Var y -> if y = x then v else t
  | App (t1, t2) -> App (substitution x v t1, substitution x v t2)
  | Abs (y, t1) ->
      if y = x then t 
      else Abs (y, substitution x v t1)
  | Int _ | EmptyList -> t  (* Rien à faire pour ces cas *)
  | Add (t1, t2) -> Add (substitution x v t1, substitution x v t2)  (* Cas pour Add *)
  | Sub (t1, t2) -> Sub (substitution x v t1, substitution x v t2)  (* Cas pour Sub *)
  | Cons (head, tail) -> Cons (substitution x v head, substitution x v tail)
  | IfZero (cond, then_br, else_br) ->
      IfZero (substitution x v cond, substitution x v then_br, substitution x v else_br)
  | IfEmpty (cond, then_br, else_br) -> 
      IfEmpty (substitution x v cond, substitution x v then_br, substitution x v else_br)
  | Let (y, t1, t2) -> 
      if y = x then Let (y, substitution x v t1, t2)
      else Let (y, substitution x v t1, substitution x v t2)
  | Fix (y, t) -> 
      if y = x then t
      else Fix (y, substitution x v t)
  
(* Mise à jour de la fonction `ltr_ctb_step` pour gérer les nouvelles fonctionnalités *)
let rec ltr_ctb_step (t : pterm) : pterm option =
  match t with
  | Var _ | Int _ | EmptyList -> None  (* Pas de réduction possible pour ces termes *)
  | Abs (x, body) -> 
      (match ltr_ctb_step body with
       | Some new_body -> Some (Abs (x, new_body))
       | None -> None)
  | App (Abs (x, t1), t2) ->
      (match ltr_ctb_step t2 with  
       | Some t2' -> Some (substitution x t2' t1)  
       | None -> Some (substitution x t2 t1))
  | App (m, n) -> 
      (match ltr_ctb_step m with  
       | Some m' -> Some (App (m', n))  
       | None -> (match ltr_ctb_step n with  
                 | Some n' -> Some (App (m, n'))  
                 | None -> None))
  | Add (Int n1, Int n2) -> Some (Int (n1 + n2))
  | Add (Int n1, t2) ->
      (match ltr_ctb_step t2 with
       | Some t2' -> Some (Add (Int n1, t2'))
       | None -> None)
  | Add (t1, t2) ->
      (match ltr_ctb_step t1 with
       | Some t1' -> Some (Add (t1', t2))
       | None -> None)
  | Sub (Int n1, Int n2) -> Some (Int (n1 - n2))
  | Sub (Int n1, t2) ->
      (match ltr_ctb_step t2 with
       | Some t2' -> Some (Sub (Int n1, t2'))
       | None -> None)
  | Sub (t1, t2) ->
      (match ltr_ctb_step t1 with
       | Some t1' -> Some (Sub (t1', t2))
       | None -> None)
  | IfZero (Int 0, then_br, _) -> Some then_br
  | IfZero (Int _, _, else_br) -> Some else_br
  | IfZero (cond, then_br, else_br) ->
      (match ltr_ctb_step cond with
       | Some cond' -> Some (IfZero (cond', then_br, else_br))
       | None -> None)
  | IfEmpty (EmptyList, then_br, _) -> Some then_br
  | IfEmpty (Cons (_, _), _, else_br) -> Some else_br
  | IfEmpty (cond, then_br, else_br) ->
      (match ltr_ctb_step cond with
       | Some cond' -> Some (IfEmpty (cond', then_br, else_br))
       | None -> None)
  | Let (x, t1, t2) ->
      (match ltr_ctb_step t1 with
       | Some t1' -> Some (Let (x, t1', t2))
       | None -> Some (substitution x t1 t2))
  | Fix (x, body) -> Some (substitution x (Fix (x, body)) body)
  | Cons (head, tail) ->
      (match ltr_ctb_step head with
       | Some head' -> Some (Cons (head', tail))
       | None -> match ltr_ctb_step tail with
                 | Some tail' -> Some (Cons (head, tail'))
                 | None -> None)
let rec alphaconv (t : pterm) : pterm =
  match t with
  | Var x -> Var x
  | App (t1, t2) -> App (alphaconv t1, alphaconv t2)
  | Abs (x, t) -> 
      let x' = nouvelle_var () in
      let t' = alphaconv t in
      substitution x (Var x') t'
  | Int _ | EmptyList -> t  (* Ces cas n'ont pas besoin de conversion *)
  | Add (t1, t2) -> Add (alphaconv t1, alphaconv t2)  (* Cas pour Add *)
  | Sub (t1, t2) -> Sub (alphaconv t1, alphaconv t2)  (* Cas pour Sub *)
  | Cons (head, tail) -> Cons (alphaconv head, alphaconv tail)
  | IfZero (cond, then_br, else_br) -> 
      IfZero (alphaconv cond, alphaconv then_br, alphaconv else_br)
  | IfEmpty (cond, then_br, else_br) -> 
      IfEmpty (alphaconv cond, alphaconv then_br, alphaconv else_br)
  | Let (x, t1, t2) -> 
      let x' = nouvelle_var () in
      Let (x', alphaconv t1, substitution x (Var x') (alphaconv t2))
  | Fix (x, t) -> 
      let x' = nouvelle_var () in
      Fix (x', substitution x (Var x') (alphaconv t))
let rec ltr_cbv_norm (t : pterm) : pterm =
  match (ltr_ctb_step t) with
  | Some reduc -> ltr_cbv_norm reduc
  | None -> t 
  
let rec ltr_cbv_norm (t : pterm) : pterm =
  match (ltr_ctb_step t) with
  | Some reduc -> ltr_cbv_norm reduc
  | None -> t 
(* Tests Arithmétiques *)
let test_add = Add (Int 2, Int 3)
let () = 
  print_endline ("2 + 3 = " ^ (print_term (ltr_cbv_norm test_add)) ^ " (attendu : Int 5)")
let test_sub = Sub (Int 7, Int 4)
let () = 
  print_endline ("7 - 4 = " ^ (print_term (ltr_cbv_norm test_sub)) ^ " (attendu : Int 3)")
let test_arith = Add (Int 2, Sub (Int 10, Int 4))
let () = 
  print_endline ("2 + (10 - 4) = " ^ (print_term (ltr_cbv_norm test_arith)) ^ " (attendu : Int 8)")
(* Tests de Conditions *)
let test_if_zero_true = IfZero (Int 0, Int 42, Int 0)
let () = 
  print_endline ("ifzero 0 then 42 else 0 = " ^ (print_term (ltr_cbv_norm test_if_zero_true)) ^ " (attendu : Int 42)")
let test_if_zero_false = IfZero (Int 5, Int 42, Int 0)
let () = 
  print_endline ("ifzero 5 then 42 else 0 = " ^ (print_term (ltr_cbv_norm test_if_zero_false)) ^ " (attendu : Int 0)")
let test_if_empty_true = IfEmpty (EmptyList, Int 1, Int 0)
let () = 
  print_endline ("ifempty [] then 1 else 0 = " ^ (print_term (ltr_cbv_norm test_if_empty_true)) ^ " (attendu : Int 1)")
let test_if_empty_false = IfEmpty (Cons (Int 1, EmptyList), Int 1, Int 0)
let () = 
  print_endline ("ifempty [1] then 1 else 0 = " ^ (print_term (ltr_cbv_norm test_if_empty_false)) ^ " (attendu : Int 0)")
(* Tests de Listes *)
let test_cons = Cons (Int 1, Cons (Int 2, EmptyList))
let () = 
  print_endline ("[1; 2] = " ^ (print_term (ltr_cbv_norm test_cons)) ^ " (attendu : Cons (Int 1, Cons (Int 2, EmptyList)))")
let test_if_empty_cons = IfEmpty (test_cons, Int 1, Int 0)
let () = 
  print_endline ("ifempty [1; 2] then 1 else 0 = " ^ (print_term (ltr_cbv_norm test_if_empty_cons)) ^ " (attendu : Int 0)")
(* Tests de Fonctions et Lambda Calculs *)
let id = Abs ("x", Var "x")
let test_id = App (id, Int 5)
let () = 
  print_endline ("id(5) = " ^ (print_term (ltr_cbv_norm test_id)) ^ " (attendu : Int 5)")
let double_apply = Abs ("f", Abs ("x", App (Var "f", App (Var "f", Var "x"))))
let increment = Abs ("y", Add (Var "y", Int 1))
let test_double_apply = App (App (double_apply, increment), Int 3)
let () = 
  print_endline ("double_apply (x + 1) (3) = " ^ (print_term (ltr_cbv_norm test_double_apply)) ^ " (attendu : Int 5)")
  (* Test de la Fonction Factorielle *)
(* Fonction factorielle corrigée utilisant la multiplication *)
let mul_by_add = 
  Fix ("mul", Abs ("n", Abs ("m",
    IfZero (Var "n", Int 0, Add (Var "m", App (App (Var "mul", Sub (Var "n", Int 1)), Var "m")))
  )))
(* Fonction factorielle corrigée utilisant la multiplication *)
let factorial = 
  Fix ("fact", Abs ("n", 
    IfZero (Var "n", Int 1, 
      App (App (mul_by_add, Var "n"), App (Var "fact", Sub (Var "n", Int 1)))
    )))
let test_factorial_5 = App (factorial, Int 5)
let () = 
  print_endline ("factorial(5) = " ^ (print_term (ltr_cbv_norm test_factorial_5)) ^ " (attendu : Int 120)")
(* Tests de l’Expression Let *)
let test_let = Let ("x", Int 3, Add (Var "x", Int 4))
let () = 
  print_endline ("let x = 3 in x + 4 = " ^ (print_term (ltr_cbv_norm test_let)) ^ " (attendu : Int 7)")
let test_let_if = Let ("x", Int 0, IfZero (Var "x", Int 42, Int 0))
let () = 
  print_endline ("let x = 0 in ifzero x then 42 else 0 = " ^ (print_term (ltr_cbv_norm test_let_if)) ^ " (attendu : Int 42)")