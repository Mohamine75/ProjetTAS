
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


  type ptype = 
  | Varp of string          (* Variable de type, par exemple, 'X' *)
  | Arr of ptype * ptype    (* Type flèche pour les fonctions, par exemple, T1 -> T2 *)
  | Nat                     (* Nouveau type pour les entiers natifs *)
  | List of ptype           (* Nouveau type pour les listes, par exemple, List T *)
  | Forall of string * ptype  (* Nouveau type polymorphe pour '∀X.T' *)

let rec print_type (t : ptype) : string =
  match t with
  | Varp x -> x
  | Arr (t1, t2) -> "(" ^ (print_type t1) ^ " -> " ^ (print_type t2) ^ ")"
  | Nat -> "N"  (* Affiche le type pour les entiers natifs *)
  | List t -> "[" ^ (print_type t) ^ "]"  (* Affiche les listes, par exemple [T] *)
  | Forall (x, t) -> "∀" ^ x ^ ". " ^ (print_type t)  (* Affiche le polymorphisme, par exemple ∀X.T *)



let compteur_var_t : int ref = ref 0
let nouvelle_var_t () : string = compteur_var := !compteur_var + 1;
  "T"^( string_of_int ! compteur_var )


type equa = (ptype * ptype) list

type env = (string * ptype) list

let rec cherche_type (v : string) (e : env) : ptype =
  match e with
  |(s,t)::reste -> if v=s then t else cherche_type v reste 
  |_ -> Nat




  let rec generaliser_type (t : ptype) (e : env) : ptype =
    let vars_in_env = List.fold_left (fun acc (_, t) -> acc @ free_type_vars t) [] e in
    let free_vars = free_type_vars t in
    let gen_vars = List.filter (fun x -> not (List.mem x vars_in_env)) free_vars in
    List.fold_right (fun x acc -> Forall (x, acc)) gen_vars t
  
  and free_type_vars (t : ptype) : string list =
    match t with
    | Varp x -> [x]
    | Arr (t1, t2) -> (free_type_vars t1) @ (free_type_vars t2)
    | List t -> free_type_vars t
    | Forall (x, t) -> List.filter ((<>) x) (free_type_vars t)
    | Nat -> []
  
let rec genere_equa (te : pterm) (ty : ptype) (e : env) : equa =
  match te with
  | Var v -> 
      let t_var = cherche_type v e in
      [(t_var, ty)]
  
  | Abs (x, t) -> 
      let ta = Varp (nouvelle_var_t ()) in
      let tr = Varp (nouvelle_var_t ()) in
      let e' = (x, ta) :: e in
      let equa_t = genere_equa t tr e' in
      (ty, Arr (ta, tr)) :: equa_t
  
  | App (t1, t2) -> 
      let ta = Varp (nouvelle_var_t ()) in
      let tr = Varp (nouvelle_var_t ()) in
      let equa_t1 = genere_equa t1 (Arr (ta, tr)) e in
      let equa_t2 = genere_equa t2 ta e in
      equa_t1 @ equa_t2

  | Int _ -> [(ty, Nat)]  (* Un entier a le type Nat *)

  | IfZero (cond, then_br, else_br) -> 
      let equa_cond = genere_equa cond Nat e in  (* La condition doit être de type Nat *)
      let equa_then = genere_equa then_br ty e in  (* Génère les équations pour le then avec cible ty *)
      let equa_else = genere_equa else_br ty e in  (* Génère les équations pour le else avec cible ty *)
      equa_cond @ equa_then @ equa_else

  | IfEmpty (cond, then_br, else_br) -> 
      let ta = Varp (nouvelle_var_t ()) in  (* Type générique pour les éléments de la liste *)
      let equa_cond = genere_equa cond (List ta) e in  (* La condition doit être de type List ta *)
      let equa_then = genere_equa then_br ty e in
      let equa_else = genere_equa else_br ty e in
      equa_cond @ equa_then @ equa_else

  | Let (x, t1, t2) -> 
      let t0 = Varp (nouvelle_var_t ()) in
      let equa_t1 = genere_equa t1 t0 e in
      let gen_t0 = generaliser_type t0 e in  (* Généraliser le type de t1 *)
      let e' = (x, gen_t0) :: e in
      let equa_t2 = genere_equa t2 ty e' in
      equa_t1 @ equa_t2

  | EmptyList -> 
      let ta = Varp (nouvelle_var_t ()) in
      [(ty, List ta)]  (* La liste vide est de type List ta pour un type quelconque ta *)

  | Add (t1, t2) -> 
      let equa_t1 = genere_equa t1 Nat e in
      let equa_t2 = genere_equa t2 Nat e in
      [(ty, Nat)] @ equa_t1 @ equa_t2  (* Addition : les deux opérandes et le résultat doivent être de type Nat *)

  | Sub (t1, t2) -> 
      let equa_t1 = genere_equa t1 Nat e in
      let equa_t2 = genere_equa t2 Nat e in
      [(ty, Nat)] @ equa_t1 @ equa_t2  (* Soustraction : même principe que pour l'addition *)

  | Cons (head, tail) -> 
      let ta = Varp (nouvelle_var_t ()) in
      let equa_head = genere_equa head ta e in
      let equa_tail = genere_equa tail (List ta) e in
      (ty, List ta) :: equa_head @ equa_tail  (* La tête doit être de type ta, et la queue de type List ta *)

  | Fix (f, body) -> 
      let tf = Varp (nouvelle_var_t ()) in  (* Type de la fonction récursive *)
      let e' = (f, tf) :: e in  (* Ajouter la fonction récursive à l'environnement *)
      let equa_body = genere_equa body tf e' in
      (ty, tf) :: equa_body  (* Le type cible ty doit être égal au type de la fonction récursive *)
    


let rec occur_check (s : string) (ty : ptype) : bool = 
  match ty with
  | Arr (t1, t2) -> (occur_check s t1) || (occur_check s t2)
  | Varp x -> x = s
  | List t -> occur_check s t
  | Forall (x, t) -> if x = s then false else occur_check s t  (* Ne pas vérifier dans une variable liée *)
  | Nat -> false


let rec substitution_type (s: string) (t_sub: ptype) (ty: ptype) : ptype =
  match ty with
  | Varp x -> if x = s then t_sub else Varp x  (* Remplace la variable de type si c'est la bonne *)
  | Arr (t1, t2) -> Arr (substitution_type s t_sub t1, substitution_type s t_sub t2)  (* Applique la substitution aux sous-types *)
  | _ -> ty  (* Sinon, on laisse le type inchangé *)
  
let rec substitution_systeme (s: string) (t_sub: ptype) (systeme: (ptype * ptype) list) : (ptype * ptype) list =
  List.map (fun (t1, t2) -> 
      (substitution_type s t_sub t1, substitution_type s t_sub t2)
    ) systeme



let rec egalite_type (t1 : ptype) (t2 : ptype) : bool = 
  match t1, t2 with
  | Varp s1, Varp s2 -> s1 = s2
  | Arr (t11, t12), Arr (t21, t22) -> (egalite_type t11 t21) && (egalite_type t12 t22)
  | Nat, Nat -> true
  | List t1', List t2' -> egalite_type t1' t2'
  | Forall (x1, t1'), Forall (x2, t2') -> 
      let t2'_renamed = substitution_type x2 (Varp x1) t2' in  (* Renommer x2 en x1 dans t2' *)
      egalite_type t1' t2'_renamed
  | _, _ -> false
    
 
let rec uni_step (eq : equa) : equa = 
  match eq with 
  | [] -> []
  | (t1, t2) :: queue -> 
      if egalite_type t1 t2 then uni_step queue
      else
        match t1, t2 with
        | Forall (x, t), _ -> 
            let t_opened = substitution_type x (Varp (nouvelle_var_t ())) t in
            uni_step ((t_opened, t2) :: queue)
        | _, Forall (x, t) -> 
            let t_opened = substitution_type x (Varp (nouvelle_var_t ())) t in
            uni_step ((t1, t_opened) :: queue)
        | List t1', List t2' -> 
            uni_step ((t1', t2') :: queue)
        | Arr (t1a, t1b), Arr (t2a, t2b) -> 
            uni_step ((t1a, t2a) :: (t1b, t2b) :: queue)
        | Varp s, _ -> 
            if occur_check s t2 then failwith "Unification échoue : occur check"
            else 
              let queue_substituee = List.map (fun (x, y) -> (substitution_type s t2 x, substitution_type s t2 y)) queue in
              (t1, t2) :: uni_step queue_substituee
        | _, Varp s -> 
            if occur_check s t1 then failwith "Unification échoue : occur check"
            else 
              let queue_substituee = List.map (fun (x, y) -> (substitution_type s t1 x, substitution_type s t1 y)) queue in
              (t1, t2) :: uni_step queue_substituee
        | _ -> failwith "Unification échoue : types incompatibles"


  let rec resoudre_systeme eq = 
    match eq with
    | [] -> Some []
    | (t1, t2) :: queue ->
        if egalite_type t1 t2 then resoudre_systeme queue
        else
          match (t1, t2) with
          | (Varp s, _) ->
              if occur_check s t2 then failwith "Unification échoue : occur check"
              else
                let new_eq = List.map (fun (x, y) -> (substitution_type s t2 x, substitution_type s t2 y)) queue in
                resoudre_systeme new_eq
          | (_, Varp s) ->
              if occur_check s t1 then failwith "Unification échoue : occur check"
              else
                let new_eq = List.map (fun (x, y) -> (substitution_type s t1 x, substitution_type s t1 y)) queue in
                resoudre_systeme new_eq
          | (Arr (t1a, t1b), Arr (t2a, t2b)) ->
              resoudre_systeme ((t1a, t2a) :: (t1b, t2b) :: queue)
          | (List t1', List t2') ->
              resoudre_systeme ((t1', t2') :: queue)
          | (Forall (x, t), _) ->
              let t_opened = substitution_type x (Varp (nouvelle_var_t ())) t in
              resoudre_systeme ((t_opened, t2) :: queue)
          | (_, Forall (x, t)) ->
              let t_opened = substitution_type x (Varp (nouvelle_var_t ())) t in
              resoudre_systeme ((t1, t_opened) :: queue)
          | _ -> failwith "Unification échoue : types incompatibles"
      

let infere_type (terme : pterm) (env : env) : ptype option =
  let nouveau_type = Varp "T" in
  let equa = genere_equa terme nouveau_type env in
  match resoudre_systeme equa with
  | Some _ -> Some nouveau_type  
  | None -> None  
                 

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


  let print_equations (eq : equa) =
    String.concat "; " (List.map (fun (t1, t2) -> print_type t1 ^ " = " ^ print_type t2) eq)
  
  let test_unification (eq : equa) =
    try
      let result = uni_step eq in
      print_endline ("Équations unifiées : " ^ print_equations result)
    with
    | Failure msg -> print_endline ("Erreur : " ^ msg)
  
  (*tests nouveau typage*)
  let eq1 = [(Forall ("X", Varp "X"), Varp "Y")]
  (* Résultat attendu : [T1 = Y], où T1 est une nouvelle variable de type *)
  
  let () = print_endline "Test 1 : Ouvrir un type ∀ à gauche";
  test_unification eq1
  let eq2 = [(Varp "Y", Forall ("X", Arr (Varp "X", Varp "X")))]
(* Résultat attendu : [Y = (T2 -> T2)], où T2 est une nouvelle variable de type *)

let () = print_endline "Test 2 : Ouvrir un type ∀ à droite";
test_unification eq2
let eq3 = [(List (Varp "A"), List (Varp "B"))]
(* Résultat attendu : [A = B] *)

let () = print_endline "Test 3 : Unification de listes";
test_unification eq3
let eq4 = [(Varp "A", Arr (Varp "B", Varp "C"))]
(* Résultat attendu : Erreur "Unification échoue : types incompatibles" *)

let () = print_endline "Test 4 : Constructeurs incompatibles";
test_unification eq4
