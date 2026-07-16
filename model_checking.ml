type state = int

type formula =
(* Linear Temporal Logic (LTL) formula representation *)
  | True
  | False
  | Empty
  | P of int
  | Not of formula
  | And of formula * formula
  | Or of formula * formula
  | Implies of formula * formula
  | G of formula
  | F of formula
  | R of formula * formula
  | U of formula * formula
  | X of formula

(*================= transformation of the formula into a Büchi Automaton =================*)


(*gives the number of the highest variable numbers in the formula*)
let rec max_var f =
    match f with 
    | G g | F g | Not g | X g -> max_var g 
    | Implies (g,h) | And (g,h) | Or (g,h) | R (g,h) | U (g,h) -> max (max_var g) (max_var h) 
    | False | True | Empty -> - 1
    | P i -> i


(* Checks if all propositional variables in the formula f are numbered from 0 to n*)
let is_var_valid f =
  let variables_vues = Hashtbl.create 16 in
  let has_negative = ref false in
  let rec aux f =
    match f with
    | True | False | Empty -> -1
    | P i -> 
        if i < 0 then has_negative := true ;
        Hashtbl.replace variables_vues i () ;
        i
    | Not g | F g | G g | X g -> aux g
    | And (g, h) | Or (g, h) | Implies (g, h) | R (g, h) | U (g, h) ->
        max (aux g) (aux h)
  in
  let max_v = aux f in
  not !has_negative && Hashtbl.length variables_vues = max_v + 1

  
let rec nnf (f:formula):formula = (*turns into Negation Normal Form*)
  match f with
  | G g -> nnf ( Not (F (Not g)) )
  | F g -> nnf ( U (True, g))
  | Implies (g,h) -> nnf ( Or (Not g, h))
  | And (g,h) -> let g' = nnf g in
                let h' = nnf h in
                And (g',h')
  | Or (g,h) -> let g' = nnf g in
                let h' = nnf h in
                Or (g',h')
  | R (g,h) -> let g' = nnf g in
               let h' = nnf h in
               R (g',h')
  | U (g,h) -> let g' = nnf g in
               let h' = nnf h in
               U (g',h')
  | X g -> let g' = nnf g in X g'
  | Not f' -> begin match f' with
              | G g -> nnf (Not ( Not (F (Not g)) ))
              | F g -> nnf (Not ( U (True, g)))
              | Implies (g,h) -> nnf (Not ( Or (Not g, h)))
              | And (g,h) -> nnf (Or (Not g,Not h))
              | Or (g,h) -> nnf (And (Not g, Not h))
              | R (g,h) -> nnf (U (Not g, Not h))
              | U (g,h) -> nnf (R (Not g, Not h))
              | Not g -> nnf g
              | X g -> nnf (X (Not g))
              | False -> True
              | True -> False
              | P i -> Not (P i)
              | Empty -> Empty
              end
  | True -> True
  | False -> False
  | P i -> P i
  | Empty -> Empty

type pre_graph =
  (* stands for previous graph. It is an intermediate data structure used as a transition from an LTL formula to a GBA.
     It is widely known as the "tableau construction".
  *)
  {nb_nodes : int ;
   nb_var : int ;                            (*variables are numbered from 0 to nb_var - 1*)
   incoming: (int, int list) Hashtbl.t;
   now: (int, formula list) Hashtbl.t ;
   next: (int, formula list) Hashtbl.t}


(* converts a formula into a pre_graph. Constraint is that it allows to afterwards create a GBA accepting the same language as f *)
let create_pre_graph (f:formula):pre_graph =
  let nb_var = max_var f + 1 in
  let max_id = ref 0 in
  let incoming_f = Hashtbl.create 30 in  (* the id as keys and an id list as values*)
  let now_f = Hashtbl.create 30 in       (* the id as keys and a formula list as values*)
  let next_f = Hashtbl.create 30 in      (* the id as keys and a formula list as values*)

  let rec expand (curr:formula list) (old:formula list) (next:formula list) (incoming:int list) =
    match curr with
    |[] -> (* verifies if there is already a state with same constraints*)
        let is_already_same_node = ref false in
        let id = ref 1 in
        while !id <= !max_id && not !is_already_same_node do
          if (begin match Hashtbl.find_opt next_f !id, Hashtbl.find_opt now_f !id with
              |None, None -> next = [] && old = []
              |None, Some l' -> next = [] && old = l'
              |Some l, None -> next = l && old = []
              |Some l, Some l' -> next = l && old = l'
              end ) (*it asks : is there a node with the same features ?*)
          then (
            begin match Hashtbl.find_opt incoming_f !id with
              |None -> Hashtbl.add incoming_f !id incoming
              |Some l -> Hashtbl.replace incoming_f !id (incoming@l)
            end ;
            is_already_same_node := true
          ) ;
          incr id
        done;
        if not !is_already_same_node then (       (* creates a new node*)
          incr max_id ;
          let new_id = !max_id in
          Hashtbl.add now_f new_id old ;
          Hashtbl.add next_f new_id next ;
          Hashtbl.add incoming_f new_id incoming ;
          expand next [] [] [new_id]
        )
    |g::curr' ->  if List.mem g old then ( expand curr' old next incoming )
                  else (
                    match g with
                    |True -> expand curr' (g::old) next incoming
                    |False -> ()
                    |P _ -> if List.mem (Not g) old then () else expand curr' (g::old) next incoming
                    |Not (P i) -> if List.mem (P i) old then () else expand curr' (g::old) next incoming
                    | And (g1,g2) -> expand (g1::g2::curr') (g::old) next incoming
                    | Or (g1,g2) -> expand (g1::curr') (g::old) next incoming ;
                                    expand (g2::curr') (g::old) next incoming
                    | U (g1,g2) -> expand (g1::curr') (g::old) (g::next) incoming ;
                                   expand (g2::curr') (g::old) next incoming
                    | R (g1,g2) -> expand (g2::curr') (g::old) (g::next) incoming ;
                                   expand (g1::g2::curr') (g::old) next incoming
                    | X g1 -> expand curr' (g::old) (g1::next) incoming
                    | _ -> failwith "not an nnf"
                  )
  in
  expand [f] [] [] [0] ;
  {nb_nodes = !max_id + 1 ; nb_var = nb_var ; incoming = incoming_f ; now = now_f ; next = next_f}


type gba =                      (* stands for Generalized Büchi Automaton *)
  {n : int;
   p : int ;                    (* number of propositional variables = size of transition arrays *)
   init : state;
   nb_final_sets : int ;        (* ids go from 0 to nb_final_sets - 1 *)
   term : int list array;       (* of size n ;  term.(q) contains the final set ids whose he belongs to *)
   delta : (state,(bool array, state) Hashtbl.t) Hashtbl.t}



let add_set_final (g:formula) (h:formula) (t: int list array) (pg:pre_graph) (id_set:int)=
  for i = 1 to pg.nb_nodes - 1 do
    begin match Hashtbl.find_opt pg.now i with
      |None -> t.(i) <- id_set::t.(i)
      |Some l -> let found = ref false in
                 let rec search l = match l with
                   |[] -> not !found
                   |x::xs -> if x = h then true
                             else ((if x = U(g,h) then found := true) ; search xs )
                 in
                 if search l then t.(i) <- id_set::t.(i)
                 (* same as : if List.mem h l || not ( List.mem (U(g,h)) l ) then ...*)
    end
  done


let final_tab (f:formula) (pg:pre_graph) =
  let final = Array.make pg.nb_nodes [] in
  let already_found = ref [] in
  let number_sets = ref 0 in
  let rec aux f =
    match f with
    | True | False | P _ | Empty | Not (P _) -> ()
    | X g -> aux g
    | And (g,h) | Or (g,h) | R (g,h) -> aux g ; aux h
    | U (g,h) -> (if not (List.mem ((g,h)) !already_found) then (
                    already_found := (g,h)::!already_found ; add_set_final g h final pg !number_sets ; incr number_sets
                 )
               ) ;
               aux g ; aux h
    | _ -> failwith "not an nnf"
  in
  aux f ;
  if !already_found = [] then (
    for i = 0 to pg.nb_nodes - 1 do
      final.(i) <- [0]
    done;
    number_sets := 1
  ) ;
  final, !number_sets


(* converts a pre_graph into a gba. The GBA will accept exacly the language as the formula f used to create the pre_graph*)
let pre_graph_to_gba (pg:pre_graph) (f:formula):gba =
  let init = 0 in
  let n = pg.nb_nodes in
  let p = pg.nb_var in
  let delta = Hashtbl.create n in
  for i = 1 to n - 1 do
    let v = Array.make p false in
    let seen = Array.make p false in
    if Hashtbl.mem pg.now i then (
      List.iter (fun g ->
        match g with
        |P j -> v.(j) <- true ; seen.(j) <- true
        |Not (P j) -> (*v.(j) <- false *) seen.(j) <- true
        | _ -> ()
      ) (Hashtbl.find pg.now i)
    ) ;
    let rec add_v j incom =
      if j = p then (
        List.iter (fun id ->
          match Hashtbl.find_opt delta id with
          |None -> let h = Hashtbl.create n in
                   Hashtbl.add h (Array.copy v) i ;
                   Hashtbl.add delta id h
          |Some h -> Hashtbl.add h (Array.copy v) i
        ) incom
      )
      else if not seen.(j) then (
        v.(j) <- false ;
        add_v (j+1) incom ;
        v.(j) <- true ;
        add_v (j+1) incom ;
      )
      else add_v (j+1) incom
    in
    match Hashtbl.find_opt pg.incoming i with
    |None -> ()
    |Some l -> add_v 0 l
  done ;
  let term, nb_sets = final_tab f pg in
  {n = n ; p = pg.nb_var ; init = init ; nb_final_sets = nb_sets ; term = term ; delta = delta}


(*========= transformation of the Generalized Büchi Automaton into a Büchi Automaton ===========*)


(* Increments a binary number represented by a boolean array (least significant bit first). *)
let increments (t:bool array):bool array =
  let n = Array.length t in
  let t' = Array.copy t in
  let i = ref 0 in
  while !i < n && t'.(!i) do
    t'.(!i) <- false;
    incr i
  done;
  if !i < n then (t'.(!i) <- true ; t')
  else t'

(* Calculates 2 raised to the power of n using a bitwise left shift. *)
let power_of_two n =
  1 lsl n


let build_set (g:gba) (s:int list) (v:bool array) =
  let t = Array.make g.n false in
  let process_state q =
    match Hashtbl.find_opt g.delta q with
    |None -> ()
    |Some h -> List.iter (fun q' -> t.(q') <- true) (Hashtbl.find_all h v)
  in
  List.iter process_state s;
  (* convert t to an ordered list of states *)
  let new_set = ref [] in
  for q = g.n - 1 downto 0 do
    if t.(q) then new_set := q :: !new_set
  done;
  !new_set


(* Determinizes the given automaton using the subset construction algorithm. *)
let powerset (g : gba) : gba =
  
  let sets = Hashtbl.create g.n in  (*key = a list of g states , value = corresponding id in the powerset construction*)
  Hashtbl.add sets [0] 0;

  let last_set = ref 0 in
  let delta' = Hashtbl.create g.n in

  (* returns (b,i) where b is true <=> 
    s is already present in sets and i the s set index (new if it didn't already exist) *)
  let add_set s =
    try (false, Hashtbl.find sets s)
    with
    | Not_found -> incr last_set;
                   Hashtbl.add sets s !last_set;
                   (true, !last_set)
  in

  (* DFS where s is a list of g states and i its corrresponding index *)
  let rec explore s i =
    let v = ref (Array.make g.p false) in
    for _ = 1 to power_of_two g.p  do
      let new_set = build_set g s !v in
      if new_set <> [] then (
        let is_new, j = add_set new_set in
        begin match Hashtbl.find_opt delta' i with
          |None -> let hi = Hashtbl.create g.n in
                   Hashtbl.add hi !v j ;
                   Hashtbl.add delta' i hi
          |Some h -> Hashtbl.add h !v j
        end ;
        if is_new then explore new_set j
      ) ;
      v := increments !v
    done
  in
  explore [0] 0;

  let n' = !last_set + 1 in

  let rec final_set = function
      | [] -> []
      | q :: qs -> g.term.(q) @ final_set qs
    in
  let term' = Array.make n' [] in
  Hashtbl.iter (fun s i -> term'.(i) <- final_set s) sets ;
  {n = n' ; p = g.p ;init = 0 ; nb_final_sets = g.nb_final_sets ; term = term' ; delta = delta'}


type ba =      (* stands for Büchi Automaton *)
  {n : int;
   p :int ;
   init : state;
   term : bool array;
   delta : (state, (bool array, state) Hashtbl.t) Hashtbl.t}


(* Converts a GBA to a BA accepting the same language. 
   It creates copies of the GBA where only one accepting set in each is accepting for the BA. And it changes copy when you encounter one.
   Please check on the Internet*)
let gba_to_ba (g:gba):ba =
  let n = g.n in
  let n' = n * g.nb_final_sets in

  (*transition*)
  let delta' = Hashtbl.create n' in
  Hashtbl.iter ( fun q h ->
    let q_set = g.term.(q) in
    for i = 0 to g.nb_final_sets - 1 do
      let hi = Hashtbl.create n in          (*   hach table of q + n*i   *)

      (* Do we change copy or not*)
      let i_arrivee = if List.mem i q_set then (i + 1) mod g.nb_final_sets else i in

      Hashtbl.iter (fun v q' ->
        Hashtbl.add hi v (q' + n*i_arrivee)
      ) h ;

      Hashtbl.add delta' (q + n*i) hi
    done
  ) g.delta ;

  (*accepting states*)
  let term' = Array.make n' false in

  for q = 0 to n - 1 do (*copy number 0*)
    if List.mem 0 g.term.(q) then term'.(q) <- true
  done;

  let init' = g.init in  (* copie numéro 0 *)

  {n = n' ; p = g.p ; init = init' ; term = term' ; delta = delta'}


(*========================= automata intersection =========================*)

let cross_product_buchi (a:ba) (b:ba):ba =
  assert (a.p = b.p) ;
  let n' = 2 * a.n * b.n in

  (*transitions*)
  let delta' = Hashtbl.create n' in
  for qa = 0 to a.n - 1 do
    for qb = 0 to b.n - 1 do
      let hqa = Hashtbl.find a.delta qa in
      let hqb = Hashtbl.find b.delta qb in
      let hqaqb1 = Hashtbl.create a.n in
      let hqaqb2 = Hashtbl.create a.n in
      Hashtbl.iter (fun v qa' ->
        if Hashtbl.mem hqb v then (
          let qb' = Hashtbl.find hqb v in
          if a.term.(qa) then Hashtbl.add hqaqb1 v (a.n*b.n + qa' + a.n*qb')  (*transition from 1 to 2*)
          else Hashtbl.add hqaqb1 v (qa' + a.n*qb') ;                         (* stays in 1*)
          if b.term.(qb) then Hashtbl.add hqaqb2 v ( qa' + a.n*qb')           (*transition from 2 to 1*)
          else Hashtbl.add hqaqb2 v (a.n*b.n + qa' + a.n*qb')                 (*stays in 2*)
        )
      ) hqa ;
      Hashtbl.add delta' (qa + a.n*qb) hqaqb1 ;
      Hashtbl.add delta' (a.n*b.n + qa + a.n*qb) hqaqb2
    done;
  done;

  (*final*)
  let term' = Array.make n' false in
  for qa = 0 to a.n - 1 do
    if a.term.(qa) then (
      for qb = 0 to b.n - 1 do
        term'.(qa + a.n*qb) <- true      (*we choose to put the tollbooth at the copy 1*)
      done
    )
  done;

  (*init*)
  let init' = a.init + a.n * b.init in      (*same we choose copy 1*)

  {n = n' ; p = a.p ; init = init' ; term = term' ; delta = delta'}



(*====== transformaton of the Kripke Structure into a Büchi Automaton =======*)

type ks =                           (* stands for kripke structure *)
  {n : state ;
   p : int ;                        (*number of propositional variables*)
   init : bool array;
   r : bool array array;            (*Adjacency matrix*)
   lab : bool array array}          (*array of size n containing bool arrays of size p*)

  
(* converts (needs to be properly described) a KS into a BA  *)
let ks_to_ba (m:ks) =
  let init' = 0 in
  let n' = m.n + 1 in               (* we add a init' hwich points at all former init states *)
  let delta' = Hashtbl.create n' in

  for i = 0 to m.n - 1 do
    let hi = Hashtbl.create n' in   (* hach table of i state neighbors *)
    for j = 0 to m.n - 1 do
      if m.r.(i).(j) then (
        let v = m.lab.(j) in
        Hashtbl.add hi v (j+1)
      )
    done;
    Hashtbl.add delta' (i+1) hi
  done;
  (* special cas of init' *)
  let h0 = Hashtbl.create n' in
  for i = 0 to m.n - 1 do
    if m.init.(i) then (
      let v = m.lab.(i) in
      Hashtbl.add h0 v (i+1)
    )
  done;
  Hashtbl.add delta' init' h0 ;

  let term' = Array.make n' true in

  {n = n' ; p = m.p ; init = init' ; term = term' ; delta = delta'}



(*======== looks if the language of the product automaton is empty or not ========*)


exception LassoFound of bool array list
(*returns : 
  None : language is empty 
  Some l : l is an example of accepting word*)
let language (a:ba) = 
  (*first graph search*)
  let seen = Array.make a.n false in
  let po = ref [] in                (*search from init until accessible terminal states in post-ordre *)
  let rec dfs x acc =
    if not seen.(x) then (
      seen.(x) <- true ;
      begin
      match Hashtbl.find_opt a.delta x with
      |None -> ()
      |Some h -> Hashtbl.iter (fun v y -> dfs y (v::acc)) h
      end ;
      if a.term.(x) then po := (x,[||]::acc)::!po
    )
  in
  dfs a.init [] ;

  (*second search to find the lasso*)
  let seen2 = Array.make a.n false in
  let rec lasso_search x target acc =
    seen2.(x) <- true ;
    begin
      match Hashtbl.find_opt a.delta x with
      |None -> ()
      |Some h -> Hashtbl.iter (fun v y ->
                   if y = target then raise (LassoFound (v::acc) )
                   else if not seen2.(y) then lasso_search y target (v::acc)
                 ) h
    end ;
  in
  try
    List.iter (fun (x,l) -> lasso_search x x l
              ) (List.rev !po) ;
    None
  with
  |LassoFound lasso -> Some (List.rev lasso)



(*============= pipeline function ==============*)

exception Not_valid_formula 

(* Checks if at least one word accepted by f and possible in the kripke structure exist.
  It raises exception Not_valid_formula is propositonal variables are not weel numbered.
  Returns : 
  None : language is empty
  Some l : l is a example word which works
*)
let model_checking (f:formula) (m:ks) =
  if is_var_valid f then (
    let f' = nnf f in
    let pg = create_pre_graph f' in
    let g = pre_graph_to_gba pg f' in
    let g' = powerset g in
    let a_formula = gba_to_ba g' in
    let a_systeme = ks_to_ba m in
    let a_cross = cross_product_buchi a_systeme a_formula in
    language a_cross
  )
  else(
    raise Not_valid_formula
  )