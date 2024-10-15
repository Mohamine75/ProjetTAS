
exception Timeout_exception 

let global_timeout = 1.0  
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
    Varp x -> x
  | Arr (t1 , t2) -> "(" ^ ( print_type t1) ^" -> "^ ( print_type t2) ^")"
  |Nat -> ""


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
      let t_var = cherche_type v e in  (* Trouver le type de la variable dans l'environnement *)
      [(t_var, ty)]  (* Générer l'équation Tv = T *)
  
  | Abs (x, t) -> 
      let ta = Varp (nouvelle_var_t ()) in  (* Créer un type frais Ta pour le paramètre *)
      let tr = Varp (nouvelle_var_t ()) in  (* Créer un type frais Tr pour le résultat *)
      let e' = (x, ta) :: e in  (* Ajouter x avec le type Ta dans l'environnement *)
      let equa_t = genere_equa t tr e' in  (* Générer les équations pour le corps de l'abs *)
      (ty, Arr (ta, tr)) :: equa_t  (* Générer l'équation Ta -> Tr = T *)
  
  | App (t1, t2) -> 
      let ta = Varp (nouvelle_var_t ()) in  (* Créer un type frais Ta pour t2 *)
      let tr = Varp (nouvelle_var_t ()) in  (* Créer un type frais Tr pour le résultat de t1 *)
      let equa_t1 = genere_equa t1 (Arr (ta, tr)) e in  (* t1 doit être de type Ta -> Tr *)
      let equa_t2 = genere_equa t2 ta e in  (* t2 doit être de type Ta *)
      equa_t1 @ equa_t2  (* Retourner la concaténation des équations *)




let rec occur_check (s:string) (ty:ptype) : bool  = 
  match ty with
  | Arr (t1,t2) -> (occur_check s t1) || (occur_check s t2)
  | Varp x -> if x=s then true else false
  | _ -> false

let rec substitution_type (s: string) (t_sub: ptype) (ty: ptype) : ptype =
  match ty with
  | Varp x -> if x = s then t_sub else Varp x  (* Remplace la variable de type si c'est la bonne *)
  | Arr (t1, t2) -> Arr (substitution_type s t_sub t1, substitution_type s t_sub t2)  (* Applique la substitution aux sous-types *)
  | _ -> ty  (* Sinon, on laisse le type inchangé *)
  
let rec substitution_systeme (s: string) (t_sub: ptype) (systeme: (ptype * ptype) list) : (ptype * ptype) list =
  List.map (fun (t1, t2) -> 
      (substitution_type s t_sub t1, substitution_type s t_sub t2)
    ) systeme



let rec egalite_type (t1 : ptype) ( t2 :ptype) : bool = 
  match t1,t2 with
  |Varp s1, Varp s2 -> s1 = s2
  |(Arr (t11,t12)),(Arr(t21,t22)) -> (egalite_type t11 t21) && (egalite_type t12  t22)
  | Nat,Nat -> true 
  | _,_ -> false
 
let rec uni_step (eq : equa) : equa = 
  match eq with 
  | [] -> []  (* Si la liste d'équations est vide, on a fini *)
  | (t1, t2) :: queue -> 
      if egalite_type t1 t2 
      then uni_step queue  (* Si les types sont égaux, on supprime l'équation *)
      else
        match t1, t2 with
        | Nat, Nat -> uni_step queue  (* Si les deux sont des types Nat, on continue *)
        | Nat, _ | _, Nat -> failwith "Unification échoue : types incompatibles avec Nat"
        | Arr (t1a, t1b), Arr (t2a, t2b) -> 
            (* Ajouter deux nouvelles équations pour les sous-types *)
            uni_step ((t1a, t2a) :: (t1b, t2b) :: queue)
        | Varp s, _ -> 
            if occur_check s t2 
            then failwith "Unification échoue : occur check"  (* Vérifier l'occurence *)
            else 
              let queue_substituee = List.map (fun (x, y) -> (substitution_type s t2 x, substitution_type s t2 y)) queue in
              (t1, t2) :: uni_step queue_substituee
        | _, Varp s -> 
            if occur_check s t1 
            then failwith "Unification échoue : occur check" 
            else 
              let queue_substituee = List.map (fun (x, y) -> (substitution_type s t1 x, substitution_type s t1 y)) queue in
              (t1, t2) :: uni_step queue_substituee


let rec resoudre_systeme eq = 
  match eq with
  | [] -> Some []  (* Si aucune équation, retourne un type vide *)
  | (t1, t2) :: queue ->
      if egalite_type t1 t2 then
        resoudre_systeme queue  (* Si les types sont égaux, continue *)
      else
        (* Traitement des cas de substitution et autres *)
        match (t1, t2) with
        | (Varp s, _) ->
            if occur_check s t2 then
              failwith "Unification échoue : occur check"
            else
              let new_eq = List.map (fun (x, y) -> (substitution_type s t2 x, substitution_type s t2 y)) queue in
              resoudre_systeme new_eq
        | (_, Varp s) ->
            if occur_check s t1 then
              failwith "Unification échoue : occur check"
            else
              let new_eq = List.map (fun (x, y) -> (substitution_type s t1 x, substitution_type s t1 y)) queue in
              resoudre_systeme new_eq
        | (Arr (t1a, t1b), Arr (t2a, t2b)) ->
            resoudre_systeme ((t1a, t2a) :: (t1b, t2b) :: queue)  (* Ajouter des sous-types pour traitement *)
        | _ -> failwith "Unification échoue : types incompatibles"
              

let infere_type (terme : pterm) (env : env) : ptype option =
  (* Générer une nouvelle variable de type pour le terme *)
  let nouveau_type = Varp "T" in
  (* Générer les équations *)
  let equa = genere_equa terme nouveau_type env in
  (* Essayer de résoudre les équations avec le timeout global *)
  match resoudre_systeme equa with
  | Some _ -> Some nouveau_type  (* Si le système est résolu, le terme est typé *)
  | None -> None  (* Sinon, le terme n'est pas typable *)  
                 

