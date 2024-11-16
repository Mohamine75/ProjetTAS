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
        (* Recherche du type dans l'environnement *)
        let t_var = 
          try cherche_type v e 
          with _ -> failwith ("Variable non trouvée : " ^ v)
        in
        [(t_var, ty)]  
    | Abs (x, t) -> 
        (* Vérifie si le type de x est déjà dans l'environnement, sinon génère une nouvelle variable *)
        let ta = 
          try cherche_type x e 
          with _ -> Varp (nouvelle_var_t ()) 
        in
        let tr = Varp (nouvelle_var_t ()) in  (* Génère un type frais pour le corps *)
        let e' = (x, ta) :: e in
        let equa_body = genere_equa t tr e' in
        (ty, Arr (ta, tr)) :: equa_body
  
    | App (t1, t2) -> 
        let ta = Varp (nouvelle_var_t ()) in  (* Génère une nouvelle variable pour l'argument *)
        let equa_t1 = genere_equa t1 (Arr (ta, ty)) e in
        let equa_t2 = genere_equa t2 ta e in
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
  | Varp x -> if x = s then t_sub else ty  (* Remplace si c'est la variable à substituer *)
  | Arr (t1, t2) -> Arr (substitution_type s t_sub t1, substitution_type s t_sub t2)  (* Applique récursivement aux sous-types *)
  | Nat -> Nat  (* Aucun changement pour Nat *) 

let rec substitution_systeme (s : string) (t_sub : ptype) (systeme :equa) : equa=
  List.map (fun (t1, t2) -> 
      (substitution_type s t_sub t1, substitution_type s t_sub t2)
    ) systeme
  


let rec appliquer_substitution (equations : (ptype * ptype) list) (t : ptype) : ptype =
  match equations with
  | [] -> t  
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
           with Not_found -> t)
      | _ -> t  
    )
;;

let rec uni_step (eq : equa) (subs : equa) : equa =
  match eq with
  | [] -> subs
  | (t1, t2) :: rest ->
      let t1' = appliquer_substitution subs t1 in
      let t2' = appliquer_substitution subs t2 in
      if egalite_type t1' t2' then
        uni_step rest subs
      else
        match (t1', t2') with
        | Varp s, _ ->
            if not (occur_check s t2') then
              let new_subs = (Varp s, t2') :: subs in
              let updated_rest = substitution_systeme s t2' rest in
              uni_step updated_rest new_subs
            else failwith "Unification échoue : occur check"
        | _, Varp s ->
            if not (occur_check s t1') then
              let new_subs = (Varp s, t1') :: subs in
              let updated_rest = substitution_systeme s t1' rest in
              uni_step updated_rest new_subs
            else failwith "Unification échoue : occur check"
        | Arr (t1a, t1b), Arr (t2a, t2b) ->
            uni_step ((t1a, t2a) :: (t1b, t2b) :: rest) subs
        | Nat, Nat -> uni_step rest subs
        | _ -> failwith "Unification échoue : types incompatibles"

  let resoudre_equations equations limit = 
  try Some (uni_step equations [])  (* Retourne simplement le résultat de uni_step, sans tuple *)
  with _ -> None
;;


let print_substitutions (equations : equa) =
  List.iter (fun (t1, t2) -> print_endline (print_type t1 ^ " = " ^ print_type t2)) equations

 let print_equation (e1, e2) =
  print_endline ("(" ^ print_type e1 ^ " = " ^ print_type e2 ^ ")")

let rec print_equations equations =
  match equations with
  | [] -> ()
  | eq :: rest -> print_equation eq; print_equations rest
;;

let trouver_variable_originale (equations : equa) (t : ptype) : ptype =
  match t with
  | Varp _ ->
      (* Rechercher une clé dans les équations dont la valeur est équivalente à `t` *)
      (try
          List.find (fun (_, t2) -> t2 = t) equations |> fst
        with Not_found -> t)
  | _ -> t

let inferer_type (term : pterm) (env : env) (limit : int) : ptype option =
  let t = Varp (nouvelle_var_t()) in
  let equations = genere_equa term t env in
  print_endline "=== Équations générées ===";
  print_equations equations;
  match resoudre_equations equations limit with
  | None -> print_endline "Échec de l'unification des équations"; None
  | Some eqs -> 
    print_endline "=== Substitutions appliquées ===";
    print_substitutions eqs; 
    let final_type = appliquer_substitution eqs t in
    let resolved_type = appliquer_substitution eqs final_type in
    let fully_resolved_type = appliquer_substitution eqs resolved_type in
    let variable_originale = trouver_variable_originale eqs fully_resolved_type in
    Some variable_originale

let  () =
  let env = [("f", Arr(Varp "B1", Varp "B2")); ("x", Varp "B1")] in
  let term = App(Var "f", Var "x") in
  match inferer_type term env 100 with
  | Some t -> print_endline ("Type inféré pour App 'f x': " ^ print_type t)
  | None -> print_endline "Erreur de typage pour App 'f x'"
;;
