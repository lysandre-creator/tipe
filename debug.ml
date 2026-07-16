open Printf
open Model_checking




let rec print_formula f = 
  match f with
  | True -> printf "True"
  | False -> printf "False"
  | P i -> printf "P %d" i 
  | Not g -> printf "Not ( " ; print_formula g ; printf " )"
  | And (g,h) -> printf "( " ; print_formula g ; printf " ) And ( " ; print_formula h ; printf " )"
  | Or (g,h) -> printf "( " ; print_formula g ; printf " ) Or ( " ; print_formula h ; printf " )"
  | Implies (g,h) -> printf "( " ; print_formula g ; printf " ) Implies ( " ; print_formula h ; printf " )"
  | G g -> printf "G ( " ; print_formula g ; printf " )" 
  | F g -> printf "F ( " ; print_formula g ; printf " )" 
  | R (g,h) -> printf "( " ; print_formula g ; printf " ) R ( " ; print_formula h ; printf " )"
  | U (g,h) -> printf "( " ; print_formula g ; printf " ) U ( " ; print_formula h ; printf " )"
  | X g -> printf "X ( " ; print_formula g ; printf " )" 
  | Empty -> printf "Empty"



let print_pre_graph (pg:pre_graph) = 
  printf "\n========================\n\n" ;
  printf "number nodes : %d\n" pg.nb_nodes ;
  printf "number var : %d\n\n" pg.nb_var ;
  let sort l = List.sort (fun x y -> x - y ) l in

  let incoming = Array.make pg.nb_nodes [] in 
  let now = Array.make pg.nb_nodes [] in 
  let next = Array.make pg.nb_nodes [] in 

  Hashtbl.iter (fun id l -> incoming.(id) <- sort l) pg.incoming ; 
  Hashtbl.iter (fun id l -> now.(id) <- l) pg.now ; 
  Hashtbl.iter (fun id l -> next.(id) <- l) pg.next ; 

  for i = 0 to pg.nb_nodes - 1 do 
    printf "%d :\n\t" i ;
    printf "incoming : " ; List.iter (fun j -> printf "%d , " j) incoming.(i) ; printf "\n\t" ;
    printf "now : " ;List.iter (fun f -> print_formula f ; printf " , ") now.(i) ; printf "\n\t" ;
    printf "next : " ;List.iter (fun f -> print_formula f ; printf " , ") next.(i) ; printf "\n\n"
  done ;
  printf "========================\n"


let print_bool_arr t =
  let len = Array.length t in 
  printf "[" ; 
  for i = 0 to  len - 2 do 
    printf " %d," (if t.(i) then 1 else 0) ;
  done;
  printf " %d ] " (if t.(len - 1) then 1 else 0)


let print_int_arr t = 
  let len = Array.length t in 
  printf "[" ; 
  for i = 0 to  len - 2 do 
    printf " %d," t.(i) ;
  done;
  printf " %d ] " t.(len - 1)

let print_int_list l = 
  let rec aux = function
    |[] -> printf "]\n" 
    |[x] -> printf "%d ]\n" x 
    |x::xs -> printf "%d ; " x ; aux xs 
  in
  printf "[ " ;
  aux l 

let print_list_arr t = 
  for i = 0 to Array.length t - 1 do
    printf "\t%d : " i ; print_int_list t.(i) 
  done

let print_gba (g:gba) =
  printf "========================\n\n" ;
  printf "number of states : %d\n" g.n ; 
  printf "number of propositional variables : %d\n" g.p ; 
  printf "initial state : %d\n" g.init ;
  printf "terminal states : \n" ; print_list_arr g.term ; printf "\n\n" ;
  let all_about_x x h = 
    printf "%d :\n" x ;
    Hashtbl.iter (fun v y ->
      printf "\t --- ";
      print_bool_arr v ;
      printf "-->  %d \n" y 
    ) h 
  in
  printf "transitions : \n" ;
  Hashtbl.iter all_about_x g.delta ;
  printf "========================\n" 


let print_ba (g:ba) =
  printf "========================\n\n" ;
  printf "number of states : %d\n" g.n ; 
  printf "number of var : %d\n" g.p ; 
  printf "initial state : %d\n" g.init ;
  printf "terminal states : " ; print_bool_arr g.term ; printf "\n\n" ;
  let all_about_x x _ = 
    printf "%d :" x ;
    let h = Hashtbl.find g.delta x in 
    Hashtbl.iter (fun v y ->
      printf "\t --- ";
      print_bool_arr v ;
      printf "-->  %d \n" y 
    ) h 
  in 
  printf "transitions : \n" ;
  Hashtbl.iter all_about_x g.delta ;
  printf "========================\n" 


let print_ks (m:ks) = 
  printf "======================\n\n" ;
  printf "number of states : %d\nnumber of propositional variables : %d\n" m.n m.p ;
  printf "initial states : number " ;
  for i = 0 to m.n - 1 do 
    if m.init.(i) then printf "%d " i 
  done;
  printf "\ntransitions :" ;
  for q = 0 to m.n - 1 do
    printf "\n%d " q ; print_bool_arr m.lab.(q) ; 
    for q' = 0 to m.n - 1 do
      if m.r.(q).(q') then printf "\n\t-------------> %d" q'
    done
  done;
  printf "\n\n==============\n" 

let rec print_lasso l = 
  match l with
  | [] -> failwith "error"
  | [x] -> 
      if Array.length x = 0 then printf "//\n"
      else (print_bool_arr x; printf " //\n")
  | h::t -> 
      if Array.length h = 0 then printf "// "
      else (print_bool_arr h; printf " --> ") ; 
      print_lasso t