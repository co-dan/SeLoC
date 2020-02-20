(* run with `ocaml bs.ml` *)
(** * Helper functions *)

(** Calculating capacity of an array *)
(* cap : int α -> int α *)
let rec cap k =
  if k = 0 then 0
  else 1 + 2*cap (k-1)

(** Comparing two `option (int a) high` values *)
(* lte_option : option (int α) high → option (int α) high → bool high *)
(* There are two cases when lte_option should return true:N
     1) Some x `lte_option` Some y <==> x <= y
     2) Some _ `lte_option` None
*)
let lte_option o1 o2 =
  let v1 = match o1 with None -> 0 | Some v -> v in
  let is_none1 = match o1 with None -> true | Some _ -> false in
  let v2 = match o2 with None -> 0 | Some v -> v in
  let is_none2 = match o2 with None -> true | Some _ -> false in
  (is_none2 || ((not is_none1) && (v1 <= v2)))  

(** Whether an option value `o` is of the form `Some v2` *)
(* eq_option : option (int α) high → int high → bool high *)
let eq_option o v2 =
  let v1 = v2+1 in
  let v1 = match o with None -> v1 | Some v -> v in
  v1 = v2

(** Displaying array as a string *)
let show_arr arr =
  Array.fold_left (fun s e ->
      match e with
      | Some v -> s ^ " " ^ string_of_int v
      | None -> s ^ " .") "" arr

(** Checks a bunch of invariants and panics if they are broken *)
let check_inv k arr =
  let rec check_padding seen_none i =
    if (i < Array.length arr) then
    (match arr.(i) with
     | None -> check_padding true (i+1)
     | Some _ -> assert (not seen_none);
                 check_padding seen_none (i+1)) in
  let rec check_sorted prev_val i =
    if (i < Array.length arr) then
    (match arr.(i) with
     | None -> ()
     | Some v -> assert (prev_val <= v);
                 check_sorted v (i+1))
  in check_padding false 0;
     check_sorted Int.min_int 0;
     assert (Array.length arr = cap k)

(** * Implementations of the main ds operations *)
(* insert_loop : ref (int low) -> ref (refN (option (int high))) ->
                 int low -> int high -> int low -> unit *)
let rec insert_loop k arr_r i x sz =
  (* k, sz are public;
     i is also public, because it only increases by one on every recursion
     x is secret *)
  (* sz = cap k initially; we just 
     pass it as a parameter to avoid recalculating it every time *)
  if (i >= sz)
  then begin
      (* time to resize the array *)
      k := !k+1;
      let arr2 = Array.make (cap (!k)) None in
      Array.blit !arr_r 0 arr2 0 sz;
      arr2.(i) <- Some x;
      arr_r := arr2
    end
  else
    match (!arr_r).(i) with
    | None -> (!arr_r).(i) <- Some x
    | Some v -> 
       (* NB: we have to keep duplicates when inserting! otherwise
              an attacker can learn the contents of the array by
              trying to force the resize operation and see if they
              succeed. *)
       (* We pre-allocate both tuples at the same time. *)
       let xv = (x, v) in
       let vx = (v, x) in
       let (p1,p2) = (if (x <= v) then xv else vx) in
       (* p1 -- element to go at the current position
          p2 -- element to continue inserting into the array *)
       (!arr_r).(i) <- Some p1;
       insert_loop k arr_r (i+1) p2 sz

(* lookup_loop : refN (option (int high)) -> int low ->
                 int high -> int high -> int high -> bool high -> bool high *)
let rec lookup_loop arr k l r x is_found =
  (* x, l, r are secret, is_found is secret too *)
  (* k is public *)
  if k = 0 then is_found
  else begin
      let i = (l+r)/2 in
      let elem = arr.(i) in
      let lr1 = (i+1, r) in
      let lr2 = (l, i-1) in
      let (l, r) = if (lte_option elem (Some x))
                   then lr1
                   else lr2 in
      let is_found = is_found || (eq_option elem x) in
      lookup_loop arr (k-1) l r x is_found
    end

type set_t = { insert : int -> unit; (* int high -> unit      *)
               lookup : int -> bool; (* int high -> bool high *)
               print : unit -> unit }

let new_set () : set_t =
  (* the size of the array is cap(k) *)
  let k = ref 1 in (* ref (int low) *)
  let arr_r = ref [|None|] in (* ref (refN (option (int high))) *)
  let insert x =
    insert_loop k arr_r 0 x (cap !k);
    check_inv !k !arr_r in
  let lookup x =
    (* we need to perform at most k iterations *)
    let r = lookup_loop !arr_r !k 0 (Array.length !arr_r) x false in
    check_inv !k !arr_r; r
  in
  { insert = (fun x -> insert x);
    lookup = (fun x -> lookup x);
    print  = (fun () -> print_endline (show_arr !arr_r))
  }

let _ =
  let s = new_set () in
  s.insert 5;
  s.insert 100;
  s.insert 3;
  s.insert 4;
  s.insert 4;
  s.insert (-5);
  s.insert (-1);
  s.insert (-1);
  s.insert (-1);
  s.insert (-3);
  s.print ();
  assert (s.lookup 3);
  assert (s.lookup 4);
  assert (s.lookup 5);
  assert (s.lookup 100);
  assert (s.lookup (-1));
  assert (s.lookup (-5));
  assert (s.lookup (-3));
  assert (not (s.lookup 11));
  assert (not (s.lookup 111));
  assert (not (s.lookup 7));
  assert (not (s.lookup 2))

