type pterm = Var of string
           | App of pterm * pterm
           | Abs of string * pterm
                    
let rec print_term (t : pterm) : string =
  match t with
    Var x -> x
  | App (t1 , t2) -> "(" ^ ( print_term t1) ^" "^ ( print_term t2) ^ ")"
  | Abs (x, t) -> "(fun " ^ x ^" -> " ^ ( print_term t) ^")"
                  
                  
let compteur_var : int ref = ref 0
    
let nouvelle_var () : string = compteur_var := ! compteur_var + 1;
  "X"^( string_of_int ! compteur_var )
    
    

let rec substitution (x : string) (v : pterm) (t : pterm) : pterm =
  match t with
  | Var y -> if y = x then v else Var y
  | App (t1, t2) -> App (subst x v t1, subst x v t2)
  | Abs (y, t1) -> if y = x then Abs (y, t1) else Abs (y, subst x v t1)


let rec alphaconv (t : pterm) : pterm =
  match t with
  | Var x -> Var x
  | App (t1, t2) -> App (alphaconv t1, alphaconv t2)
  | Abs (x, t) ->
      let new_var = nouvelle_var () in
      let t' = subst x (Var new_var) t in
      Abs (new_var, alphaconv t')

        
      let t4 = Abs ("x", Abs ("y", App (Var "x", Var "y"))) ;;
      let result4 = alphaconv t4 ;;
      print_endline (print_term result4) ;;
      
      
      