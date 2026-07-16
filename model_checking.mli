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

val nnf : formula -> formula


type pre_graph = {   
  (* stands for previous graph. It is an intermediate data structure used as a transition from an LTL formula to a GBA.
     It is widely known as the "tableau construction".
  *)
  nb_nodes : int;
  nb_var : int;
  incoming : (int, int list) Hashtbl.t;
  now : (int, formula list) Hashtbl.t;
  next : (int, formula list) Hashtbl.t;
}

val create_pre_graph : formula -> pre_graph

type gba = {
  (* stands for Generalized Büchi Automaton *)
  n : int;
  p : int;
  init : state;
  nb_final_sets : int;
  term : int list array;
  delta : (state, (bool array, state) Hashtbl.t) Hashtbl.t;
}

val powerset : gba -> gba

type ba = {
  (* stands for Büchi Automaton *)
  n : int;
  p : int;
  init : state;
  term : bool array;
  delta : (state, (bool array, state) Hashtbl.t) Hashtbl.t;
}

val gba_to_ba : gba -> ba

val cross_product_buchi : ba -> ba -> ba

type ks = {
  (* stands for Kripke Structure *)
  n : state;
  p : int;
  init : bool array;
  r : bool array array;
  lab : bool array array;
}

val ks_to_ba : ks -> ba

exception LassoFound of bool array list

val language : ba -> bool array list option

exception Not_valid_formula

val model_checking : formula -> ks -> bool array list option

