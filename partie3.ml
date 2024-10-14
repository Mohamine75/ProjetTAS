
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
      [(cherche_type v e, ty)]

  | App (t1, t2) -> 
      let ta = Varp (nouvelle_var_t ()) in
      let equa_t1 = genere_equa t1 (Arr (ta, ty)) e in
      let equa_t2 = genere_equa t2 ta e in
      equa_t1 @ equa_t2

  | Abs (x, t) -> 
      let ta = Varp (nouvelle_var_t ()) in
      let e' = (x, ta) :: e in
      let tr = Varp (nouvelle_var_t ()) in 
      let equa_t = genere_equa t tr e' in
      let equa_abs = [(ty, Arr(ta, tr))] in
      equa_abs @ equa_t

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
      | Varp s, _ -> 
          if occur_check s t2 
          then failwith "Unification échoue : occur check"  (* Vérifier l'occurence *)
          else 
            (* Substitution de la variable s par t2 dans le reste des équations *)
            let queue_substituee = List.map (fun (x, y) -> (substitution_type s t2 x, substitution_type s t2 y)) queue in
            uni_step queue_substituee
      | _, Varp s -> 
          if occur_check s t1 
          then failwith "Unification échoue : occur check" 
          else 
            let queue_substituee = List.map (fun (x, y) -> (substitution_type s t1 x, substitution_type s t1 y)) queue in
            uni_step queue_substituee
      | Arr (t1a, t1b), Arr (t2a, t2b) -> 
          (* Ajouter deux nouvelles équations pour les sous-types *)
          uni_step ((t1a, t2a) :: (t1b, t2b) :: queue)
      | _ -> failwith "Unification échoue : types incompatibles"