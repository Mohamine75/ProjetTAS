

type pterm = Var of string
           | App of pterm * pterm
           | Abs of string * pterm
           
let rec print_term (t : pterm) : string =
  match t with
    Var x -> x
  | App (t1, t2) -> "(" ^ (print_term t1) ^ " " ^ (print_term t2) ^ ")"
  | Abs (x, t) -> "(fun " ^ x ^ " -> " ^ (print_term t) ^ ")"

let compteur_var : int ref = ref 0

let nouvelle_var () : string = 
  compteur_var := !compteur_var + 1;
  "X" ^ (string_of_int !compteur_var)
  
let rec isValeur (t : pterm) : bool = 
  match t with
  | Var _ -> true
  | Abs (_, _) -> true
  | App(t1, t2) -> (match t1 with 
      | Var _ -> isValeur t2  
      | _ -> false)
    
let rec alphaconv (t : pterm) : pterm =
  match t with
  | Var x -> Var x 
  | App (t1, t2) -> App (alphaconv t1, alphaconv t2)  
  | Abs (x, t) -> 
      let x' = nouvelle_var () in 
      let t' = alphaconv t in  
      match t' with
      | Abs (y, body) when y = x -> Abs (x', body) 
      | _ -> Abs (x', t')
      
let rec substitution (x : string) (v : pterm) (t : pterm) : pterm =
  match t with
  | Var y -> if y = x then v else t
  | App (t1, t2) -> App (substitution x v t1, substitution x v t2)
  | Abs (y, t1) ->
      if y = x then t  
      else 
        Abs (y, substitution x v t1)  



let rec ltr_ctb_step (t : pterm) : pterm option =
  match t with
  | Var _ -> None
  | Abs (x, body) -> 
    (match ltr_ctb_step body with
     | Some new_body -> Some (Abs (x, new_body))
     | None -> None)  | App (Abs (x, t1), t2) ->
        (match ltr_ctb_step t2 with  
        | Some t2' -> Some (substitution x t2' t1)  
        | None -> Some(substitution x t2 t1) )
  | App (m, n) -> 
      match ltr_ctb_step m with  
      | Some m' -> Some (App (m', n))  
      | None -> match ltr_ctb_step n with  
                | Some n' -> Some (App (m, n'))  
                | None -> None  
            

let rec ltr_cbv_norm (t : pterm) : pterm =
  match (ltr_ctb_step t) with
  | Some reduc -> ltr_cbv_norm reduc
  | None -> t 

let i = Abs("x", Var "x")
let k = Abs("x", Abs("y", Var "x"))
let s = Abs("x", Abs("y", Abs("z", App(App(Var "x", Var "z"), App(Var "y", Var "z")))))

let skk = App(App(s,k),k)
let ii = App((k,k))
let result = ltr_cbv_norm(skk)
let () = print_endline (print_term result)


let church_zero = Abs("f", Abs("x", Var "x"))
let church_one = Abs("f", Abs("x", App(Var "f", Var "x")))
let church_two = Abs("f", Abs("x", App(Var "f", App(Var "f", Var "x"))))
let church_three = Abs("f", Abs("x", App(Var "f", App(Var "f", App(Var "f", Var "x")))))

let successeur = Abs("n", Abs("f", Abs("x", App(Var "f", App(App(Var "n", Var "f"), Var "x")))))
let addition = Abs("m", Abs("n", Abs("f", Abs("x", App(App(Var "m", Var "f"), App(App(Var "n", Var "f"), Var "x"))))))
let multiplication = Abs("m", Abs("n", Abs("f", App(Var "m", App(Var "n", Var "f")))))

let puissance = Abs("m", Abs("n", Abs("f", Abs("x", App(App(Var "n", App(Var "m", Var "f")), Var "x")))))

let test_church () =
  let result_succ = ltr_cbv_norm (App(successeur, church_two)) in
  let result_add = ltr_cbv_norm (App(App(addition, church_one), church_two)) in
  let result_mult = ltr_cbv_norm (App(App(multiplication, church_two), church_three)) in
  let result_pow = ltr_cbv_norm (App(App(puissance, church_two), church_three)) in
  print_endline ("Successeur de 2 (attendu 3) : " ^ print_term result_succ);
  print_endline ("1 + 2 (attendu 3) : " ^ print_term result_add);
  print_endline ("2 * 3 (attendu 6) : " ^ print_term result_mult);
  print_endline ("2 ^ 3 (attendu 8) : " ^ print_term result_pow)


let () = test_church ()

