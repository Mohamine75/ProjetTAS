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

let compteur_var_t : int ref = ref 0
let nouvelle_var_t () : string = 
  compteur_var_t := !compteur_var_t + 1;
  "T" ^ (string_of_int !compteur_var_t)
let nouvelle_var () : string = 
  compteur_var := !compteur_var + 1;
  "X" ^ (string_of_int !compteur_var)

  type ptype = 
  | Varp of string  
  | Arr of ptype * ptype  
  | Nat  
  | List of ptype  
  | Forall of string * ptype 
  | R


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

let rec print_type (t : ptype) : string =
  match t with
  | Varp x -> x
  | Arr (t1, t2) -> "(" ^ (print_type t1) ^ " -> " ^ (print_type t2) ^ ")"
  | Nat -> "Nat"
  | List t -> "[" ^ (print_type t) ^ "]"
  | Forall (x, t) -> "∀" ^ x ^ "." ^ (print_type t)
  | R -> "R"




let rec cherche_type (v : string) (e : env) : ptype =
  match e with
  | (s, t) :: reste -> if v = s then t else cherche_type v reste
  | _ -> failwith ("Variable non trouvée : " ^ v)

let rec open_forall (x : string) (t : ptype) : ptype =
  match t with
  | Varp y when y = x -> Varp (nouvelle_var ())  
  | Forall (y, t') when y = x -> open_forall y t' 
  | Forall (y, t') -> Forall (y, open_forall x t') 
  | _ -> t  
  
  
  let rec genere_equa (te : pterm) (ty : ptype) (e : env) : equa =
    match te with
    | Var v -> 
        let t_var = cherche_type v e in
        [(t_var, ty)] 
    | Int _ -> 
        [(Nat, ty)]  
    | Abs (x, t) -> 
        let ta = 
          try cherche_type x e 
          with _ -> Varp (nouvelle_var_t ())  
        in
        let tr = Varp (nouvelle_var_t ()) in  
        let e' = (x, ta) :: e in  
        let equa_body = genere_equa t tr e' in  
        (ty, Arr (ta, tr)) :: equa_body 
  
    | App (t1, t2) -> 
        let ta = Varp (nouvelle_var_t ()) in  
        let equa_t1 = genere_equa t1 (Arr (ta, ty)) e in
            let equa_t2 = genere_equa t2 ta e in  
        equa_t1 @ equa_t2
    | EmptyList -> 
        [(Varp "T", ty)]  
    | Cons (head, tail) -> 
        let t_head = Varp (nouvelle_var_t ()) in
        let t_tail = Varp (nouvelle_var_t ()) in
        let equa_head = genere_equa head t_head e in
        let equa_tail = genere_equa tail (Arr (t_head, t_tail)) e in
        equa_head @ equa_tail  
       | IfEmpty (cond, t1, t2) ->
          let ta = Varp (nouvelle_var_t()) in
          let eq_cond = genere_equa cond (List ta) e in
          let eq_t1 = genere_equa t1 ty e in
          let eq_t2 = genere_equa t2 ty e in
          eq_cond @ eq_t1 @ eq_t2
    | Fix (x, t) -> 
        let ta = Varp (nouvelle_var_t ()) in
        let tr = Varp (nouvelle_var_t ()) in
        let e' = (x, ta) :: e in
        let equa_body = genere_equa t tr e' in
        [(ty, Arr (ta, tr))] @ equa_body  
    | Let (x, t1, t2) -> 
        let ta = Varp (nouvelle_var_t ()) in
        let equa_t1 = genere_equa t1 ta e in
        let e' = (x, ta) :: e in
        let equa_t2 = genere_equa t2 ty e' in
        equa_t1 @ equa_t2
        | Add (t1, t2) ->
          let equa_t1 = genere_equa t1 Nat e in 
          let equa_t2 = genere_equa t2 Nat e in 
          (ty, Nat) :: equa_t1 @ equa_t2 
      | Sub (t1, t2) ->
          let equa_t1 = genere_equa t1 Nat e in  
          let equa_t2 = genere_equa t2 Nat e in  
          (ty, Nat) :: equa_t1 @ equa_t2  
      | IfZero (cond, t1, t2) -> 
          let tc = genere_equa cond R e in
          let eq_t1 = genere_equa t1 ty e in
          let eq_t2 = genere_equa t2 ty e in
          tc @ eq_t1 @ eq_t2


  let rec occur_check (s:string) (ty: ptype) : bool = 
    match ty with
    | Arr (t1, t2) -> (occur_check s t1) || (occur_check s t2) 
    | Varp x -> if x = s then true else false  
    | Forall (x, t) -> if x = s then false else occur_check s t  
    | List t -> occur_check s t  
    | R -> false 
    | _ -> false 
        

let rec substitution_type (s : string) (t_sub : ptype) (ty : ptype) : ptype =
  match ty with
  | Varp x -> if x = s then t_sub else ty 
  | Arr (t1, t2) -> Arr (substitution_type s t_sub t1, substitution_type s t_sub t2) 
  | Nat -> Nat  
  
let rec substitution_systeme (s : string) (t_sub : ptype) (systeme :equa) : equa=
  List.map (fun (t1, t2) -> 
      (substitution_type s t_sub t1, substitution_type s t_sub t2)
    ) systeme
  
    let rec egalite_type (t1 : ptype) (t2 : ptype) : bool =
      match t1, t2 with
      | Varp s1, Varp s2 -> s1 = s2
      | Arr (t11, t12), Arr (t21, t22) -> egalite_type t11 t21 && egalite_type t12 t22
      | Nat, Nat -> true
      | R, R -> true
      | Forall (x, t1'), Forall (y, t2') -> egalite_type t1' t2'
      | List t1, List t2 -> egalite_type t1 t2
      | _, _ -> false
    
  let rec uni_step (eq : (ptype * ptype) list) (subs : (ptype * ptype) list) : (ptype * ptype) list =
    match eq with
    | [] -> subs  (* Retourne les substitutions accumulées quand il n'y a plus d'équations *)
  
    | (t1, t2) :: rest -> 
        if egalite_type t1 t2 then
          uni_step rest subs  (* Si les types sont égaux, on passe à l'équation suivante *)
        else
          match (t1, t2) with
          | Varp s, _ ->  (* Si t1 est une variable de type *)
              if not (occur_check s t2) then  (* Vérifie si on n'a pas de conflit dans l'occurence *)
                let new_subs = (Varp s, t2) :: subs in  (* Ajoute la substitution de la variable *)
                let updated_rest = substitution_systeme s t2 rest in  (* Applique la substitution aux autres équations *)
                uni_step updated_rest new_subs  (* Continue avec les nouvelles équations et substitutions *)
              else 
                failwith "Unification échoue : occur check"
  
          | _, Varp s ->  (* Si t2 est une variable de type *)
              if not (occur_check s t1) then  (* Vérifie si on n'a pas de conflit dans l'occurence *)
                let new_subs = (Varp s, t1) :: subs in  (* Ajoute la substitution de la variable *)
                let updated_rest = substitution_systeme s t1 rest in  (* Applique la substitution aux autres équations *)
                uni_step updated_rest new_subs  (* Continue avec les nouvelles équations et substitutions *)
              else 
                failwith "Unification échoue : occur check"
  
          | Arr (t1a, t1b), Arr (t2a, t2b) ->  (* Si ce sont des flèches (fonctions) *)
              let new_eqs = (t1a, t2a) :: (t1b, t2b) :: rest in  (* Décompose les équations en sous-types *)
              uni_step new_eqs subs  (* Continue avec les nouvelles équations et substitutions *)
  
          | Nat, Nat -> uni_step rest subs  (* Les types Nat sont déjà égaux, on les ignore *)
  
          | List t1, List t2 ->  (* Si ce sont des listes *)
              let new_eq = (t1, t2) :: rest in  (* On unifie les types des éléments des listes *)
              uni_step new_eq subs  (* Continue avec l'unification des éléments de liste *)
  
          | Forall (x, t1'), _ ->  (* Si t1 est un type universel (∀x. t1) *)
              (* Appliquer la "barendregtisation" : ouvrir ∀x et renommer x si nécessaire *)
              let t1_open = open_forall x t1' in
              let new_eq = (t1_open, t2) :: rest in
              uni_step new_eq subs
  
          | _, Forall (x, t2') ->  (* Si t2 est un type universel (∀x. t2) *)
              (* Appliquer la "barendregtisation" : ouvrir ∀x et renommer x si nécessaire *)
              let t2_open = open_forall x t2' in
              let new_eq = (t1, t2_open) :: rest in
              uni_step new_eq subs
  
          | _ -> failwith "Unification échoue : types incompatibles"
  
let resoudre_equations equations limit = 
  try Some (uni_step equations [])  (* Retourne simplement le résultat de uni_step, sans tuple *)
  with _ -> None
;;

let rec appliquer_substitution (equations : (ptype * ptype) list) (t : ptype) : ptype =
  match equations with
  | [] -> t  (* Si aucune équation, on retourne le type inchangé *)
  | (Varp v, t') :: rest -> 
      appliquer_substitution rest (substitution_type v t' t)
  | _ -> (
      match t with
      | Arr (t1, t2) -> 
          Arr (appliquer_substitution equations t1, appliquer_substitution equations t2)
      | Varp x -> 
          (try 
             let (_, t_sub) = List.find (fun (Varp v, _) -> v = x) equations in
             t_sub
           with Not_found -> t)  (* Sinon, garder le type inchangé *)

      | List t' -> 
          (* Si t est une liste, appliquer les substitutions sur le type des éléments *)
          List (appliquer_substitution equations t')

      | Forall (x, t') -> 
          (* Si t est un type quantifié (∀x. t'), appliquer les substitutions sur t' 
             mais ignorer les variables quantifiées *)
          let t_sub = appliquer_substitution equations t' in
          Forall (x, t_sub)

      | _ -> t  (* Pour tous les autres types (Nat, etc.), pas de substitution nécessaire *)
  )
;;


let inferer_type (term : pterm) (env : env) (limit : int) : ptype option =
  let t = Varp (nouvelle_var_t()) in
  let equations = genere_equa term t env in
  match resoudre_equations equations limit with
  | None -> print_endline "echec de l'unification des equations"; None
  | Some eqs -> 
    let final_type = appliquer_substitution eqs t in
    Some final_type
;;
                 
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


  let  () =
  let env = [("f", Arr(Varp "B1", Varp "B2")); ("x", Varp "B1")] in
  let term = App(Var "f", Var "x") in
  match inferer_type term env 100 with
  | Some t -> print_endline ("Type inféré pour App 'f x': " ^ print_type t)
  | None -> print_endline "Erreur de typage pour App 'f x'"
;;
