open Printf
open Debug 
open Examples
open Model_checking

let () = Printexc.record_backtrace true


let main () = 
  let t0 = Sys.time () in
  try 
    match model_checking wgc_formula_all_in_formula wgc_ks_all_in_formula with 
    | None -> printf "Execution time : %f seconds\n" (Sys.time() -. t0) ; printf "No solution found.\n"
    | Some l -> printf "Execution time : %f seconds\n" (Sys.time() -. t0) ; printf "A solution has been found ! It is : \n" ; print_lasso l 
  
  with
  | Not_valid_formula -> printf "Please give a valid formula. \n"

let () = 
  main ()