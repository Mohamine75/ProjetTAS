
let compteur_var : int ref = ref 0

type pterm = Var of string
| App of pterm * pterm
| Abs of string * pterm
let nouvelle_var () : string = 
  compteur_var := !compteur_var + 1;
  "X" ^ (string_of_int !compteur_var)

type ptype = Var of string | Arr of ptype * ptype | Nat
let rec print_type (t : ptype) : string =
  match t with
  Var x -> x
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
      let ta = Var (nouvelle_var_t ()) in
      let equa_t1 = genere_equa t1 (Arr (ta, ty)) e in
      let equa_t2 = genere_equa t2 ta e in
      equa_t1 @ equa_t2

  | Abs (x, t) -> 
      let ta = Var (nouvelle_var_t ()) in
      let e' = (x, ta) :: e in
      let tr = Var (nouvelle_var_t ()) in 
      let equa_t = genere_equa t tr e' in
      let equa_abs = [(ty, Arr(ta, tr))] in
      equa_abs @ equa_t

let rec occur_check (s:string) (ty:ptype) : bool  = 
  match ty with
  | Arr (t1,t2) -> (occur_check s t1) || (occur_check s t2)
  | Var x -> if x=s then true else false
  | _ -> false

