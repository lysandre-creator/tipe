open Model_checking


(* ==================== Some concrete variables to run tests on ================= *)

let f1 = (G (Implies (P 1, F (P 2))))
let f2 = (Not (R (P 1,P 2)))

let ba1:ba = 
  let h0 = Hashtbl.create 2 in 
  Hashtbl.add h0 [|true ; false|] 1 ;
  Hashtbl.add h0 [|false; true|] 0 ;
  let h1 = Hashtbl.create 2 in 
  Hashtbl.add h1 [|true ; false|] 0 ;
  Hashtbl.add h1 [|false; true|] 0 ;
  let h = Hashtbl.create 2 in 
  Hashtbl.add h 0 h0 ;
  Hashtbl.add h 1 h1 ;
  {n = 2 ; p = 2 ;init = 0 ; term = [|false; true|] ; delta = h}

let ba2:ba = 
  let h0 = Hashtbl.create 2 in 
  Hashtbl.add h0 [|true ; false|] 1 ;
  Hashtbl.add h0 [|false; true|] 0 ;
  let h1 = Hashtbl.create 1 in 
  Hashtbl.add h1 [|false ; true|] 0 ;
  let h = Hashtbl.create 2 in 
  Hashtbl.add h 0 h0 ;
  Hashtbl.add h 1 h1 ;
  {n = 2 ; p = 2 ; init = 0 ; term = [|true; false|] ; delta = h}



let gba1:gba = 
  let h0 = Hashtbl.create 3 in 
  Hashtbl.add h0 [|true ; false|] 1 ;
  Hashtbl.add h0 [|false ; true|] 2 ; 
  Hashtbl.add h0 [|true ; true|] 0 ;
  let h1 = Hashtbl.create 1 in 
  Hashtbl.add h1 [|true ; true|] 0 ;
  let h2 = Hashtbl.create 1 in
  Hashtbl.add h2 [|true ; true|] 0 ; 
  let h = Hashtbl.create 3 in 
  Hashtbl.add h 0 h0 ;
  Hashtbl.add h 1 h1 ;
  Hashtbl.add h 2 h2 ;
  {n = 3 ; p = 2 ; init = 0 ; nb_final_sets = 2 ; term = [| [] ; [0] ; [1]|] ; delta = h}

let gba1bis:gba = (*almost the same but which 2 accepting states per group of accepting states*)
  let h0 = Hashtbl.create 5 in 
  Hashtbl.add h0 [|true ; false ; false ; false|] 1 ;
  Hashtbl.add h0 [|false ; true ; false ; false|] 2 ; 
  Hashtbl.add h0 [|false ; false ; true ; false|] 3 ; 
  Hashtbl.add h0 [|false ; false ; false ; true|] 4 ; 
  Hashtbl.add h0 [|true ; true ; true ; true|] 0 ;
  let h1 = Hashtbl.create 1 in 
  Hashtbl.add h1 [|true ; true ; true ; true|] 0 ;
  let h2 = Hashtbl.create 1 in
  Hashtbl.add h2 [|true ; true ; true ; true|] 0 ; 
  let h3 = Hashtbl.create 1 in 
  Hashtbl.add h3 [|true ; true ; true ; true|] 0 ;
  let h4 = Hashtbl.create 1 in 
  Hashtbl.add h4 [|true ; true ; true ; true|] 0 ;
  let h = Hashtbl.create 5 in 
  Hashtbl.add h 0 h0 ;
  Hashtbl.add h 1 h1 ;
  Hashtbl.add h 2 h2 ;
  Hashtbl.add h 3 h3 ;
  Hashtbl.add h 4 h4 ; 
  {n = 5 ; p = 4 ; init = 0 ; nb_final_sets = 2 ; term = [| [] ; [0] ; [0] ; [1] ; [1] |] ; delta = h}





(* ========================== Structures for the wolf, goat and cabbage Problem ===========================*)
(* Let's call it the wgc game*)

 (*****************************************************************************
 * WOLF, GOAT, AND CABBAGE (WGC) PUZZLE
 *
 * The objective of the game is to transport a Man, a Wolf, a Goat, and a 
 * Cabbage across a river to the opposite side (from true to false).
 *
 *
 * RULES:
 * 1. Movement Rule: The Man must drive the boat and can take at most one passenger.
 *    The passenger must be on the same side as the Man before the move.
 * 2. Safety Rule: The Wolf cannot be left alone with the Goat. The Goat cannot 
 *    be left alone with the Cabbage.
 *
 * VARIABLES:
 * P 0 = Man | P 1 = Wolf | P 2 = Goat | P 3 = Cabbage
 * true = Starting side
 * false = Finish side
 *
 * BELOW ARE THREE MODELING APPROACHES:
 * - Case 1 (KS-heavy): Both Movement and Safety Rules are in the KS, Formula is simple.
 * - Case 1 (Half-and-Half): Movement Rule is in the KS, Safety Rule is in the Formula.
 * - Case 2 (Formula-heavy): Both Movement and Safety Rules are in the Formula, KS is free.
 *****************************************************************************)

(* --- SHARED FUNCTIONS AND FORMULAS --- *)

let is_move_valid t t' =
  if t.(0) = t'.(0) then t = t'
  else
    let move1 = t.(1) <> t'.(1) in
    let move2 = t.(2) <> t'.(2) in
    let move3 = t.(3) <> t'.(3) in
    
    let nb_moves = (if move1 then 1 else 0) + (if move2 then 1 else 0) + (if move3 then 1 else 0) in
    
    let valid_moves = 
      (not move1 || t.(1) = t.(0)) &&
      (not move2 || t.(2) = t.(0)) &&
      (not move3 || t.(3) = t.(0))
    in
    
    nb_moves <= 1 && valid_moves

let is_safe t =
  let wolf_eats_goat = (t.(1) = t.(2)) && (t.(0) <> t.(1)) in
  let goat_eats_cabbage = (t.(2) = t.(3)) && (t.(0) <> t.(2)) in
  not (wolf_eats_goat || goat_eats_cabbage)

let three_and f1 f2 f3 = And (f1 , And (f2,f3) )
let four_and f1 f2 f3 f4 = And ( And (f1,f2) , And (f3,f4) ) 

(* Objective : everyone is on the other side of the river (the "false" side) *)
let win = four_and (Not (P 0)) (Not (P 1)) (Not (P 2)) (Not (P 3))

(* Defeat conditions : Wolf eats Goat or Goat eats Cabbage *)
let defeat =
  Or (
    Or (     (*Wolf eats Goat *)
      three_and (P 1) (P 2) (Not (P 0))          (* Wolf and Goat are on the starting side and Man on the finish side *)
      ,
      three_and (Not (P 1)) (Not (P 2)) (P 0)    (* Wolf and Goat are on the finish side and Man on the starting side *)
    ) 
    ,
    Or (     (* Goat eats Cabbage *)
      three_and (P 2) (P 3) (Not (P 0))           (* Goat and Cabbage are on the starting side and Man on the finish side *)
      ,
      three_and (Not (P 2)) (Not (P 3)) (P 0)     (* Goat and Cabbage are on the finish side and Man on the starting side *)
    )
  )


(* ========================================================================= *)
(* CASE 1 : ALL IN KS                                                        *)
(* The Kripke Structure enforces both the Movement Rule and the Safety Rule. *)
(* The Formula only asks if the win state can be reached.                    *)
(* ========================================================================= *)

let wgc_ks_all_in_ks:ks =
  let bin_to_bool b = if b = 0 then false else true in
  let lab1 = Array.make 16 [||] in
  for h = 0 to 1 do
    for w = 0 to 1 do
      for m = 0 to 1 do
        for c = 0 to 1 do
          lab1.(h*2*2*2 + w*2*2 + m*2 + c) <- [|bin_to_bool h ; bin_to_bool w ; bin_to_bool m ; bin_to_bool c|] 
        done
      done
    done
  done;
  let init1 = Array.make 16 false in 
  init1.(15) <- true ;
  let r1 = Array.make_matrix 16 16 false  in
  for i = 0 to 15 do
    for j = 0 to i do 
      if is_safe lab1.(i) && is_safe lab1.(j) && is_move_valid lab1.(i) lab1.(j) then (
        r1.(i).(j) <- true ; 
        if j <> 0 then  (* we want the state 0 = [ 0 0 0 0] to be a sink state *)
          r1.(j).(i) <- true 
      )
    done;
  done;
  
  {n = 16 ; p = 4 ; init = init1 ; r = r1 ; lab = lab1}

let wgc_formula_all_in_ks = U (True, win)


(* ========================================================================= *)
(* CASE 2 : HALF AND HALF                                                    *)
(* The Kripke Structure enforces the Movement Rule.                          *)
(* The Formula enforces the Safety Rule (avoiding defeat) and the goal.      *)
(* ========================================================================= *)

let wgc_ks_half_half:ks =
  let bin_to_bool b = if b = 0 then false else true in
  let lab1 = Array.make 16 [||] in
  for h = 0 to 1 do
    for w = 0 to 1 do
      for m = 0 to 1 do
        for c = 0 to 1 do
          lab1.(h*2*2*2 + w*2*2 + m*2 + c) <- [|bin_to_bool h ; bin_to_bool w ; bin_to_bool m ; bin_to_bool c|] 
        done
      done
    done
  done;
  let init1 = Array.make 16 false in 
  init1.(15) <- true ;
  let r1 = Array.make_matrix 16 16 false  in
  for i = 0 to 15 do
    for j = 0 to i do 
      if is_move_valid lab1.(i) lab1.(j) then (
        r1.(i).(j) <- true ; 
        if j <> 0 then  (* we want the state 0 = [ 0 0 0 0] to be a sink state *)
          r1.(j).(i) <- true 
      )
    done;
  done;
  
  {n = 16 ; p = 4 ; init = init1 ; r = r1 ; lab = lab1}

let wgc_formula_half_half = U (Not defeat, win)


(* ========================================================================= *)
(* CASE 3 : ALL IN FORMULA                                                   *)
(* The Kripke Structure allows all transitions (complete graph).             *)
(* The Formula enforces both the Movement Rule and the Safety Rule.          *)
(* ========================================================================= *)

let wgc_ks_all_in_formula:ks =
  let bin_to_bool b = if b = 0 then false else true in
  let lab1 = Array.make 16 [||] in
  for h = 0 to 1 do
    for w = 0 to 1 do
      for m = 0 to 1 do
        for c = 0 to 1 do
          lab1.(h*2*2*2 + w*2*2 + m*2 + c) <- [|bin_to_bool h ; bin_to_bool w ; bin_to_bool m ; bin_to_bool c|] 
        done
      done
    done
  done;
  let init1 = Array.make 16 false in 
  init1.(15) <- true ;
  let r1 = Array.make_matrix 16 16 false in
  for i = 0 to 15 do
    for j = 0 to 15 do
      if i = 0 then 
        r1.(i).(j) <- (i = j) (* we want the state 0 = [ 0 0 0 0] to be a sink state *)
      else 
        r1.(i).(j) <- true
    done;
  done;
  
  {n = 16 ; p = 4 ; init = init1 ; r = r1 ; lab = lab1}

(* Logical encoding of the Movement Rule *)
let iff f1 f2 = And (Implies (f1, f2), Implies (f2, f1))
let xor f1 f2 = Or (And (f1, Not f2), And (Not f1, f2))

let eq_next p = iff (P p) (X (P p))
let diff_next p = xor (P p) (X (P p))

let no_move = four_and (eq_next 0) (eq_next 1) (eq_next 2) (eq_next 3)

let move_wolf = 
  four_and (iff (P 0) (P 1)) (diff_next 0) (diff_next 1) (And (eq_next 2, eq_next 3))

let move_goat = 
  four_and (iff (P 0) (P 2)) (diff_next 0) (diff_next 2) (And (eq_next 1, eq_next 3))

let move_cabbage = 
  four_and (iff (P 0) (P 3)) (diff_next 0) (diff_next 3) (And (eq_next 1, eq_next 2))

let move_man_only = 
  four_and (diff_next 0) (eq_next 1) (eq_next 2) (eq_next 3)

let valid_move = 
  Or (no_move, Or (move_wolf, Or (move_goat, Or (move_cabbage, move_man_only))))

let wgc_formula_all_in_formula = 
  And (G valid_move, U (Not defeat, win))