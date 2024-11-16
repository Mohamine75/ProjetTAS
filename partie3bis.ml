let compteur_var : int ref = ref 0

type pterm = Var of string
           | App of pterm * pterm
           | Abs of string * pterm
let nouvelle_var () : string = 
  compteur_var := !compteur_var + 1;
  "X" ^ (string_of_int !compteur_var)

type ptype = Varp of string | Arr of ptype * ptype | Nat
let rec print_type (t : ptype) : string =
  match t with
  | Varp x -> x
  | Arr (t1, t2) -> "(" ^ (print_type t1) ^ " -> " ^ (print_type t2) ^ ")"
  | Nat -> "Nat"



let compteur_var_t : int ref = ref 0
let nouvelle_var_t () : string = 
  compteur_var_t := !compteur_var_t + 1;
  "T" ^ (string_of_int !compteur_var_t)


type equa = (ptype * ptype) list

type env = (string * ptype) list

let rec cherche_type (v : string) (e : env) : ptype =
  match e with
  | (s, t) :: reste -> if v = s then t else cherche_type v reste
  | _ -> failwith ("Variable non trouvée : " ^ v)


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

let rec occur_check (s : string) (ty : ptype) : bool =
  match ty with
  | Arr (t1, t2) -> (occur_check s t1) || (occur_check s t2)
  | Varp x -> if x = s then true else false
  | _ -> false
        
  let rec egalite_type (t1 : ptype) ( t2 :ptype) : bool = 
    match t1,t2 with
    |Varp s1, Varp s2 -> s1 = s2
    |(Arr (t11,t12)),(Arr(t21,t22)) -> (egalite_type t11 t21) && (egalite_type t12  t22)
    | Nat,Nat -> true 
    | _,_ -> false

let rec substitution_type (s : string) (t_sub : ptype) (ty : ptype) : ptype =
  match ty with
  | Varp x -> if x = s then t_sub else Varp x  (* Remplace si c'est la variable à substituer *)
  | Arr (t1, t2) -> Arr (substitution_type s t_sub t1, substitution_type s t_sub t2)  (* Applique récursivement aux sous-types *)
  | Nat -> Nat  (* Aucun changement pour Nat *)

  let rec substitution_systeme (s : string) (t_sub : ptype) (systeme : (ptype * ptype) list) : (ptype * ptype) list =
    List.map (fun (t1, t2) -> 
        (substitution_type s t_sub t1, substitution_type s t_sub t2)
      ) systeme
  

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
              
              


                    let timeout (f : unit -> 'a option) (timeout_duration : float) : 'a option =
                      let start_time = Sys.time () in
                      let rec loop () =
                        if (Sys.time () -. start_time) > timeout_duration then
                          None  (* Timeout atteint *)
                        else
                          match f () with
                          | Some result -> Some result
                          | None -> loop ()
                      in
                      loop ()
                    
                    let resoudre_avec_timeout (eq : (ptype * ptype) list) (timeout_duration : float) : ((ptype * ptype) list * (string * ptype) list) option =
                      timeout (fun () -> resoudre_systeme eq [] 100) timeout_duration  (* 100 itérations max *)
                    

  let resoudre_avec_timeout (eq : (ptype * ptype) list) (timeout_duration : float) : ((ptype * ptype) list * (string * ptype) list) option =
    timeout (fun () -> resoudre_systeme eq [] 100) (timeout_duration +. 5.0)  (* Augmenter le timeout *)
  
    let t1 = Var "x"
    let env1 = [("x", Varp "A")]
    let equa1 = genere_equa t1 (Varp "T") env1
    let () = 
      match resoudre_systeme equa1 [] 10 with
      | Some (equa, _) -> List.iter (fun (t1, t2) -> Printf.printf "%s = %s\n" (print_type t1) (print_type t2)) equa
      | None -> Printf.printf "Non typable\n"
      let t2 = Abs ("x", Var "x")
      let env2 = []
      let equa2 = genere_equa t2 (Varp "T") env2
      let () = 
        match resoudre_systeme equa2 [] 10 with
        | Some (equa, _) -> List.iter (fun (t1, t2) -> Printf.printf "%s = %s\n" (print_type t1) (print_type t2)) equa
        | None -> Printf.printf "Non typable\n"
        let t3 = App (Abs ("x", Var "x"), Var "y")
        let env3 = [("y", Varp "B")]  (* Environnement : y a pour type B *)
        let equa3 = genere_equa t3 (Varp "T") env3
        
        let () = 
          match resoudre_systeme equa3 [] 10 with
          | Some (equa, _) -> List.iter (fun (t1, t2) -> Printf.printf "%s = %s\n" (print_type t1) (print_type t2)) equa
          | None -> Printf.printf "Non typable\n"
        