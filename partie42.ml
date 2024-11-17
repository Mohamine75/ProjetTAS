exception Timeout_exception 
let global_timeout = 1.0  
let compteur_var : int ref = ref 0
type pterm =
  | Var of string
  | App of pterm * pterm
  | Abs of string * pterm
  | Int of int
  | Add of pterm * pterm
  | Sub of pterm * pterm
  | IfZero of pterm * pterm * pterm
  | EmptyList
  | Cons of pterm * pterm
  | IfEmpty of pterm * pterm * pterm
  | Fix of string * pterm
  | Let of string * pterm * pterm
  | Head of pterm   
  | Tail of pterm   

  
let nouvelle_var () : string = 
  compteur_var := !compteur_var + 1;
  "X" ^ (string_of_int !compteur_var)
type ptype =
| Varp of string           
| Arr of ptype * ptype     
| Nat                      
| List of ptype            
| Forall of string * ptype 


let rec print_type (t : ptype) : string =
  match t with
  | Varp x -> x
  | Arr (t1, t2) -> "(" ^ (print_type t1) ^ " -> " ^ (print_type t2) ^ ")"
  | Nat -> "Nat"
  | List t -> "[" ^ (print_type t) ^ "]"
  | Forall (x, t) -> "∀" ^ x ^ ". " ^ (print_type t)



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
  | Head t1 -> "(head " ^ (print_term t1) ^ ")"  (* Ajout pour Head *)
  | Tail t1 -> "(tail " ^ (print_term t1) ^ ")"  (* Ajout pour Tail *)

  let compteur_var_t : int ref = ref 0
let nouvelle_var_t () : string = compteur_var := !compteur_var + 1;
  "T"^( string_of_int ! compteur_var )
type equa = (ptype * ptype) list
type env = (string * ptype) list


let rec variables_type_libres (t : ptype) : string list =
  match t with
  | Varp x -> [x]
  | Arr (t1, t2) -> (variables_type_libres t1) @ (variables_type_libres t2)
  | Nat -> []
  | List t1 -> variables_type_libres t1
  | Forall (x, t1) -> List.filter (fun y -> y <> x) (variables_type_libres t1)


let rec variables_type_env (env : env) : string list =
  match env with
  | [] -> []
  | (_, t) :: rest -> (variables_type_libres t) @ (variables_type_env rest)


let generaliser_type (t : ptype) (env : env) : ptype =
  let var_libres_t = variables_type_libres t in
  let var_libres_env = variables_type_env env in
  let var_a_generaliser = List.filter (fun v -> not (List.mem v var_libres_env)) var_libres_t in
  List.fold_left (fun acc var -> Forall (var, acc)) t var_a_generaliser
  
let rec cherche_type (v : string) (e : env) : ptype =
  match e with
  |(s,t)::reste -> if v=s then t else cherche_type v reste 
  |_ -> failwith ("Variable non trouvée : " ^ v)
  let rec genere_equa (te : pterm) (ty : ptype) (e : env) : equa =
    match te with
    | Var v -> 
        let t_var = 
          try cherche_type v e 
          with _ -> failwith ("Variable non trouvée : " ^ v)
        in
        [(t_var, ty)]
  
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
  
    | Int _ -> 
        [(ty, Nat)]
  
    | Add (t1, t2) | Sub (t1, t2) ->
        [(ty, Nat)] @ genere_equa t1 Nat e @ genere_equa t2 Nat e
  
    | IfZero (cond, then_br, else_br) ->
        let equa_cond = genere_equa cond Nat e in
        let equa_then = genere_equa then_br ty e in
        let equa_else = genere_equa else_br ty e in
        equa_cond @ equa_then @ equa_else
  
    | EmptyList -> 
        [(ty, List (Varp (nouvelle_var_t ())))]
  
    | Cons (head, tail) ->
        let ta = Varp (nouvelle_var_t ()) in
        let equa_head = genere_equa head ta e in
        let equa_tail = genere_equa tail (List ta) e in
        [(ty, List ta)] @ equa_head @ equa_tail
  
    | IfEmpty (cond, then_br, else_br) ->
        let ta = Varp (nouvelle_var_t ()) in
        let equa_cond = genere_equa cond (List ta) e in
        let equa_then = genere_equa then_br ty e in
        let equa_else = genere_equa else_br ty e in
        equa_cond @ equa_then @ equa_else
  
    | Let (x, e1, e2) ->
        let t0 = Varp (nouvelle_var_t ()) in
        let equa_e1 = genere_equa e1 t0 e in
        let t0_gen = generaliser_type t0 e in
        let e' = (x, t0_gen) :: e in
        let equa_e2 = genere_equa e2 ty e' in 
        equa_e1 @ equa_e2
    | Head t ->
      let ta = Varp (nouvelle_var_t ()) in
      let equa_t = genere_equa t (List ta) e in
      [(ty, ta)] @ equa_t  (* Le type de Head t doit être égal au type des éléments de la liste *)

    | Tail t ->
        let ta = Varp (nouvelle_var_t ()) in
        let equa_t = genere_equa t (List ta) e in
        [(ty, List ta)] @ equa_t  (* Le type de Tail t doit être une liste des mêmes éléments *)
  
  
let rec occur_check (s:string) (ty:ptype) : bool  = 
  match ty with
  | Arr (t1,t2) -> (occur_check s t1) || (occur_check s t2)
  | Varp x -> if x=s then true else false
  | _ -> false

  let rec substitution_type (s : string) (t_sub : ptype) (ty : ptype) : ptype =
    match ty with
    | Varp x -> if x = s then t_sub else ty
    | Arr (t1, t2) -> Arr (substitution_type s t_sub t1, substitution_type s t_sub t2)
    | Nat -> Nat
    | List t1 -> (
        match t_sub with
        | List _ -> substitution_type s t_sub t1  (* Évite la double liste *)
        | _ -> List (substitution_type s t_sub t1)
      )
    | Forall (x, t1) ->
        if x = s then ty
        else Forall (x, substitution_type s t_sub t1)
  
  
  let rec substitution_systeme (s : string) (t_sub : ptype) (systeme : (ptype * ptype) list) : (ptype * ptype) list =
    List.map (fun (t1, t2) -> 
        (substitution_type s t_sub t1, substitution_type s t_sub t2)
      ) systeme
  
let rec egalite_type (t1 : ptype) (t2 : ptype) : bool =
  match (t1, t2) with
  | Varp s1, Varp s2 -> s1 = s2
  | Arr (t11, t12), Arr (t21, t22) -> (egalite_type t11 t21) && (egalite_type t12 t22)
  | Nat, Nat -> true
  | List t1, List t2 -> egalite_type t1 t2
  | Forall (x1, t1), Forall (x2, t2) ->
      let t1_renamed = substitution_type x1 (Varp x2) t1 in
      egalite_type t1_renamed t2
  | _, _ -> false
      
 
  let appliquer_substitution (equations : (ptype * ptype) list) (t : ptype) : ptype =
    let rec appliquer_une_substitution (s : string) (t_sub : ptype) (ty : ptype) : ptype =
      match ty with
      | Varp x -> if x = s then t_sub else ty
      | Arr (t1, t2) -> Arr (appliquer_une_substitution s t_sub t1, appliquer_une_substitution s t_sub t2)
      | List t1 -> List (appliquer_une_substitution s t_sub t1)
      | Forall (x, t1) ->
          if x = s then ty
          else Forall (x, appliquer_une_substitution s t_sub t1)
      | Nat -> Nat
    in
  
    let rec appliquer_toutes_substitutions ty =
      List.fold_left (fun acc (Varp v, t_sub) -> appliquer_une_substitution v t_sub acc) ty equations
    in
  
    let rec fixer_point ty =
      let ty' = appliquer_toutes_substitutions ty in
      if egalite_type ty ty' then ty'
      else fixer_point ty'
    in
  
    fixer_point t
  
  


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


let print_substitutions (equations : equa) =
  List.iter (fun (t1, t2) -> print_endline (print_type t1 ^ " = " ^ print_type t2)) equations

  let print_equation (e1, e2) =
  print_endline ("(" ^ print_type e1 ^ " = " ^ print_type e2 ^ ")")

let rec print_equations equations =
  match equations with
  | [] -> ()
  | eq :: rest -> print_equation eq; print_equations rest
;;
                

let resoudre_equations equations limit = 
  try Some (uni_step equations []) 
  with _ -> None
;;

let trouver_variable_originale (equations : equa) (t : ptype) : ptype =
  match t with
  | Varp _ ->
      (try
          List.find (fun (_, t2) -> t2 = t) equations |> fst
        with Not_found -> t)
  | _ -> t
                
let infere_type (term : pterm) (env : env) (limit : int) : ptype option =
  let t = Varp (nouvelle_var_t()) in
  let equations = genere_equa term t env in
  print_endline "=== Équations générées ===";
  print_equations equations;
  match  resoudre_equations equations limit with
  | None -> print_endline "Échec de l'unification des équations"; None
  | Some eqs -> 
    print_endline "=== Substitutions appliquées ===";
    print_substitutions eqs; 
    let final_type = appliquer_substitution eqs t in
    let resolved_type = appliquer_substitution eqs final_type in
    let fully_resolved_type = appliquer_substitution eqs resolved_type in
    let variable_originale = trouver_variable_originale eqs fully_resolved_type in
    Some variable_originale 


let rec isValeur (t : pterm) : bool = 
  match t with
  | Var _ -> true
  | Abs (_, _) -> true
  | Int _ -> true 
  | EmptyList -> true 
  | Cons (head, tail) -> isValeur head && isValeur tail 
  | _ -> false 

let rec substitution (x : string) (v : pterm) (t : pterm) : pterm =
  match t with
  | Var y -> if y = x then v else t
  | App (t1, t2) -> App (substitution x v t1, substitution x v t2)
  | Abs (y, t1) ->
      if y = x then t 
      else Abs (y, substitution x v t1)
  | Int _ | EmptyList -> t  
  | Add (t1, t2) -> Add (substitution x v t1, substitution x v t2)
  | Sub (t1, t2) -> Sub (substitution x v t1, substitution x v t2)
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
  | Head t1 -> Head (substitution x v t1) 
  | Tail t1 -> Tail (substitution x v t1)  
  
  
let rec ltr_ctb_step (t : pterm) : pterm option =
  match t with
  | Var _ | Int _ | EmptyList -> None  
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
  | Head (Cons (head, _)) -> Some head  
  | Head t1 -> 
      (match ltr_ctb_step t1 with
       | Some t1' -> Some (Head t1')
       | None -> failwith ("Liste vide, impossible de faire head"))
  | Tail (Cons (_, tail)) -> Some tail  
  | Tail t1 ->
      (match ltr_ctb_step t1 with
       | Some t1' -> Some (Tail t1')
       | None -> failwith ("Liste vide, impossible de faire tail"))
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
| Int _ | EmptyList -> t 
| Add (t1, t2) -> Add (alphaconv t1, alphaconv t2)
| Sub (t1, t2) -> Sub (alphaconv t1, alphaconv t2)
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
| Head t1 -> Head (alphaconv t1) 
| Tail t1 -> Tail (alphaconv t1) 
      
let rec ltr_cbv_norm (t : pterm) : pterm =
  match (ltr_ctb_step t) with
  | Some reduc -> ltr_cbv_norm reduc
  | None -> t 

(* Test 1: Simple variable *)
let test_1 = Var "x"
let env_1 = [("x", Varp "A")]
let result_1 = infere_type test_1 env_1 10
let () = 
  match result_1 with
  | Some t -> print_endline ("Test 1 - Type inféré: " ^ print_type t)
  | None -> print_endline "Test 1 - Non typable"

(* Test 2: Fonction identité *)
let test_2 = Abs ("x", Var "x")
let env_2 = []
let result_2 = infere_type test_2 env_2 10
let () = 
  match result_2 with
  | Some t -> print_endline ("Test 2 - Type inféré: " ^ print_type t)
  | None -> print_endline "Test 2 - Non typable"

(* Test 3: Application de fonction *)
let test_3 = App (Abs ("x", Var "x"), Var "y")
let env_3 = [("y", Varp "A")]
let result_3 = infere_type test_3 env_3 10
let () = 
  match result_3 with
  | Some t -> print_endline ("Test 3 - Type inféré: " ^ print_type t)
  | None -> print_endline "Test 3 - Non typable"

(* Test 4: Fonction polymorphe *)
let test_4 = Abs ("x", Abs ("y", Var "x"))
let env_4 = []
let result_4 = infere_type test_4 env_4 10
let () = 
  match result_4 with
  | Some t -> print_endline ("Test 4 - Type inféré: " ^ print_type t)
  | None -> print_endline "Test 4 - Non typable"

(* Test 5: Application de fonction polymorphe *)
let test_5 = App (App (Abs ("x", Abs ("y", Var "x")), Var "a"), Var "b")
let env_5 = [("a", Varp "A"); ("b", Varp "B")]
let result_5 = infere_type test_5 env_5 10
let () = 
  match result_5 with
  | Some t -> print_endline ("Test 5 - Type inféré: " ^ print_type t)
  | None -> print_endline "Test 5 - Non typable"

(* Test 6: Arithmétique simple *)
let test_6 = Add (Int 2, Int 3)
let env_6 = []
let result_6 = infere_type test_6 env_6 10
let () = 
  match result_6 with
  | Some t -> print_endline ("Test 6 - Type inféré: " ^ print_type t)
  | None -> print_endline "Test 6 - Non typable"

(* Test 7: Condition IfZero *)
let test_7 = IfZero (Int 0, Int 42, Int 0)
let env_7 = []
let result_7 = infere_type test_7 env_7 10
let () = 
  match result_7 with
  | Some t -> print_endline ("Test 7 - Type inféré: " ^ print_type t)
  | None -> print_endline "Test 7 - Non typable"

(* Test 8: Liste vide *)
let test_8 = EmptyList
let env_8 = []
let result_8 = infere_type test_8 env_8 10
let () = 
  match result_8 with
  | Some t -> print_endline ("Test 8 - Type inféré: " ^ print_type t)
  | None -> print_endline "Test 8 - Non typable"

(* Test 9: Liste avec un élément *)
let test_9 = Cons (Int 1, EmptyList)
let env_9 = []
let result_9 = infere_type test_9 env_9 10
let () = 
  match result_9 with
  | Some t -> print_endline ("Test 9 - Type inféré: " ^ print_type t)
  | None -> print_endline "Test 9 - Non typable"

(* Test 10: Let-in *)
let test_10 = Let ("x", Int 3, Add (Var "x", Int 4))
let env_10 = []
let result_10 = infere_type test_10 env_10 10
let () = 
  match result_10 with
  | Some t -> print_endline ("Test 10 - Type inféré: " ^ print_type t)
  | None -> print_endline "Test 10 - Non typable"
