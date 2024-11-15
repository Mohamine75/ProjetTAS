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
      let ta = 
        try cherche_type x e  (* Si le type de x est déjà défini dans l'environnement *)
        with _ -> Varp (nouvelle_var_t ())  (* Sinon, on génère un type frais pour x *)
      in
      let tr = Varp (nouvelle_var_t ()) in  (* Génère un type frais pour le résultat de l'abs *)
      let e' = (x, ta) :: e in  (* Ajouter x avec son type dans l'environnement *)
      let equa_body = genere_equa t tr e' in  (* Générer les équations pour le corps de la fonction *)
      (ty, Arr (ta, tr)) :: equa_body  (* L'abs a le type Arr (ta, tr) *)
  
  | App (t1, t2) -> 
      let ta = Varp (nouvelle_var_t ()) in  (* Type pour l'argument de t1 *)  
      let equa_t1 = genere_equa t1 (Arr (ta, ty)) e in  (* Générer les équations pour t1 de type fonction *)
  
        (* t2 doit être de type ta, c'est-à-dire le type attendu pour l'argument de la fonction *)
      let equa_t2 = genere_equa t2 ta e in  (* Générer les équations pour t2, l'argument de la fonction *)
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

        | _ -> failwith "Unification échoue : types incompatibles"
                        
let resoudre_equations equations limit = 
  try Some (uni_step equations [])  (* Retourne simplement le résultat de uni_step, sans tuple *)
  with _ -> None
;;



let rec appliquer_substitution (equations : (ptype * ptype) list) (t : ptype) : ptype =
  match equations with
  | [] -> t  (* Si aucune équation, on retourne le type inchangé *)
  | (Varp v, t') :: rest -> 
      (* Si t1 est une variable de type (Varp), on applique la substitution *)
      appliquer_substitution rest (substitution_type v t' t)
  | _ -> (
      match t with
      | Arr (t1, t2) -> 
          (* Si le type est une fonction, appliquer les substitutions sur les sous-types *)
          Arr (appliquer_substitution equations t1, appliquer_substitution equations t2)
      | Varp x -> 
          (* Si t est une variable de type, vérifier si une substitution est appliquée *)
          (try 
             (* Si une substitution existe pour cette variable, l'appliquer *)
             let (_, t_sub) = List.find (fun (Varp v, _) -> v = x) equations in
             t_sub
           with Not_found -> t)  (* Sinon, garder le type inchangé *)
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

let t4 = Abs ("x", Abs ("y", Var "x"))
let env4 = []
let result4 = inferer_type t4 env4 10
let () = match result4 with
  | Some t -> Printf.printf "Test 4 - Type inféré: %s\n" (print_type t)
  | None -> Printf.printf "Test 4 - Non typable\n"
