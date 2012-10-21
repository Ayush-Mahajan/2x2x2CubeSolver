#use "fold.ml";;

type turn = R | R' | R2 | F | F' | F2 | U | U' | U2
type scramble = turn list
type algorithm = scramble
type piece = UBL | UBR | UFR | UFL | DBL | DBR | DFR | DFL
type orientation = O | CW | CCW
type position = piece
type corner = piece * orientation
type cubie = position * corner
type cube = cubie list

let solved_cube : cubie list = 
  [(UBL, (UBL,O)); (UBR, (UBR,O)); (UFR, (UFR,O)); (UFL, (UFL,O));
  (DBL, (DBL,O)); (DBR, (DBR,O)); (DFR, (DFR,O)); (DFL, (DFL,O))]

let get_inverse_turn = function
  | F -> F'
  | F' -> F
  | F2 -> F2
  | R -> R'
  | R' -> R
  | R2 -> R2
  | U -> U'
  | U' -> U
  | U2 -> U2

(* Swaps UFL and UFR while maintaining their orientations *)
let permute_corners =
  [U'; R; U; R'; F'; R; U; R'; U'; R'; F; R2; U'; R']

(* Twists UFL counterclockwise and UFR clockwise *)
let orient_corners =
  [R; U; R'; U; R; U2; R2; U'; R; U'; R'; U2; R]

(* Returns setup moves to move corner at pos1 to UFL and pos2 to UFR *)
(* Maintains both corners' orientations after moving                 *)
let get_setup_moves (pos1 : position) (pos2 : position) : algorithm =
  if pos1 = pos2 then failwith "The two positions have to be different"
  else match pos1, pos2 with
    | UFL, UFR -> []
    | UFL, UBR -> [U; R'; U'; R]
    | UFL, UBL -> [U; R2; F2; U']
    | UFL, DFL -> [U2; R2; F2]
    | UFL, DFR -> [U; F2; U']
    | UFL, DBR -> [R2]
    
    | UFR, UFL -> [U2; R2; F2; U']
    | UFR, UBR -> [U]
    | UFR, UBL -> [U2; R'; U'; R]
    | UFR, DFL -> [U'; R2; F2]
    | UFR, DFR -> [U2; F2; U']
    | UFR, DBR -> [U; R2]
    
    | UBR, UFL -> [U'; R'; U'; R]
    | UBR, UFR -> [U'; R2; F2; U']
    | UBR, UBL -> [U2]
    | UBR, DFL -> [R2; F2]
    | UBR, DFR -> [U'; F2; U']
    | UBR, DBR -> [U2; R2]
    
    | UBL, UFL -> [U']
    | UBL, UFR -> [R'; U'; R]
    | UBL, UBR -> [R2; F2; U']
    | UBL, DFL -> [U; R2; F2]
    | UBL, DFR -> [F2; U']
    | UBL, DBR -> [U'; R2]
    
    | DFL, UFL -> [U2; F2; U]
    | DFL, UFR -> [U'; F2; U]
    | DFL, UBR -> [F2; U]
    | DFL, UBL -> [U; F2; U]
    | DFL, DFR -> [R2; F2; U]
    | DFL, DBR -> [F2; U; R2]
    
    | DFR, UFL -> [U; R2; U2]
    | DFR, UFR -> [U2; R2; U2]
    | DFR, UBR -> [U'; R2; U2]
    | DFR, UBL -> [R2; U2]
    | DFR, DFL -> [F2]
    | DFR, DBR -> [F2; R2]
    
    | DBR, UFL -> [F2; R2; U]
    | DBR, UFR -> [U; F2; R2; U]
    | DBR, UBR -> [U2; F2; R2; U]
    | DBR, UBL -> [U'; F2; R2; U]
    | DBR, DFL -> [F2; R2; U; R2]
    | DBR, DFR -> [R2; U]
    
    | _ -> failwith "DBL always has correct orientation and permutation"

(* ----------------------------------------------------------------------- *)
(* Hashtable helpers *)

(* Given a list of (key, value) pairs, return a corresponding hash table *)
let make_hashtbl (lst : ('a * 'b) list) : ('a, 'b) Hashtbl.t =
  let hashtbl = Hashtbl.create (List.length lst) in
  let _ = List.iter (fun (key, value) -> Hashtbl.add hashtbl key value) lst in
  hashtbl

let hashtbl_add hsh k v = Hashtbl.add hsh k v; hsh

let hashtbl_find = Hashtbl.find

let in_hashtbl = Hashtbl.mem

(* ----------------------------------------------------------------------- *)
(* Other helpers *)

(* Returns an int list of length num, initialized with 0 *)
let get_list num = Array.to_list (Array.make num 0)

(* Initialize Random so it won't use the default seed *)
let _ = Random.self_init()

(* ----------------------------------------------------------------------- *)
(* Moving cube *)

let state_checker (c:cube) : bool =
 (* Reject anything of without 8 pieces *)
 if (List.length c !=8) then false else
 (* Returns a list of the pieces/corners *) 
 let getCorners (c:cube) : piece list =
  let foo = fun acc ele -> fst(snd ele)::acc in
   List.fold_left foo [] c in
 (* Returns a list of positions in the cube *) 
 let getPositions (c:cube) : position list =
  let foo = fun acc ele -> fst(ele)::acc in
   List.fold_left foo [] c in
 (* Define an appropriate comparison standard between 2 pieces *)
 let comparator (p1:piece) (p2:piece) : int =
  if (p1<p2) then 1 else 
  if (p1=p2) then 0 else -1 in
 (* Ensures presence of all the corners and positions *)
 let ordered_pos = [DFL; DFR; DBR; DBL; UFL; UFR; UBR; UBL] in
 if (not (List.sort comparator (getCorners c)=ordered_pos)  ||
  not(List.sort comparator (getPositions c)=ordered_pos)) then false else
 (* Returns the count of orientation o supplied in the cube *)   
 let count (c:cube) (o:orientation) =
  let foo = fun acc ele -> if (snd (snd ele)==o) then acc+1 else acc in
   List.fold_left foo 0 c in 
 (* Ensures a correct distribution of orientations *)
 if (((count c CW) - (count c CCW)) mod 3 != 0) then false else 
 (* Checks whether the cube c has (DBL,(DBL,O)) *)
 let checkDBL (c:cube) =
  let foo acc ele = 
   acc || ((fst ele)==DBL && fst(snd ele)==DBL && snd(snd ele) == O) in
   List.fold_left foo false c in
 checkDBL c;;

(* Moving cube *)
let move (c:cube) (t:turn) : cube =
 (* Get the corner at position p in cube c *)
 let getCornerAt (p:position) (c:cube) : corner = 
  let foo acc ele = if(fst(ele) = p) then snd(ele) else acc in
   List.fold_left foo (DBL,O) c in
 (* Set position p of cube c to corner c1 *)
 let setCornerAt (c:cube) (p:position) (c1:corner) : cube = 
  let foo acc ele = if(fst(ele) = p) then (fst(ele),c1)::acc else ele::acc in
   List.fold_left foo [] c in
 (* Adds the orientation o to the corner c *)
 let turn_corner (c:corner) (o:orientation) : corner =
  let add_orientation (o1:orientation) (o2:orientation) =
   match o1 with 
   | O -> o2
   | CW -> (match o2 with
           | O -> CW
           | CW -> CCW
           | CCW -> O)
   | CCW -> (match o2 with 
           | O -> CCW
           | CW -> O
           | CCW -> CW) in
   (fst(c),(add_orientation (snd(c)) o)) in
 (* Defining the move U by the definitions given in the problem *)
 let move_u (c:cube) : cube=
  let a1 = setCornerAt c UBL (getCornerAt UFL c) in
   let a2 = setCornerAt a1 UBR (getCornerAt UBL c) in
    let a3 = setCornerAt a2 UFR (getCornerAt UBR c) in
     setCornerAt a3 UFL (getCornerAt UFR c) in
 (* Defining the move R by the definitions given in the problem *)
 let move_r (c:cube) : cube =
  let a1 = setCornerAt c UBR (turn_corner (getCornerAt UFR c) CW) in
   let a2 = setCornerAt a1 UFR (turn_corner (getCornerAt DFR c) CCW)in
    let a3 = setCornerAt a2 DBR (turn_corner (getCornerAt UBR c) CCW) in
     setCornerAt a3 DFR (turn_corner (getCornerAt DBR c) CW) in
 (* Defining the move F by the definition given in the problem *)
 let move_f (c:cube) : cube =
  let a1 = setCornerAt c UFR (turn_corner (getCornerAt UFL c) CW) in
   let a2 = setCornerAt a1 UFL (turn_corner (getCornerAt DFL c) CCW)in
    let a3 = setCornerAt a2 DFR (turn_corner (getCornerAt UFR c) CCW) in
     setCornerAt a3 DFL (turn_corner (getCornerAt DFR c) CW) in
 (* Defining move U' *)
 let move_u' (c:cube) : cube=
  move_u (move_u (move_u (c))) in
 (* Defining move U2 *)
 let move_u2 (c:cube) : cube =
  move_u (move_u (c)) in
 (* Defining move R' *)
 let move_r' (c:cube) : cube =
  move_r (move_r (move_r (c))) in
 (* Defining move R2 *)
 let move_r2 (c:cube) : cube =
  move_r (move_r (c)) in
 (* Defining move F' *)
 let move_f' (c:cube) : cube =
  move_f (move_f (move_f (c))) in
 (* Defining move F2 *)
 let move_f2 (c:cube) : cube =
  move_f (move_f (c)) in
 (* Matching input move with correct redirection *)
 match t with 
  | R -> move_r c
  | R' -> move_r' c
  | R2 -> move_r2 c
  | F -> move_f c
  | F' -> move_f' c
  | F2 -> move_f2 c
  | U -> move_u c
  | U' -> move_u' c
  | U2 -> move_u2 c;;


(* Given an algorithm and a cube, return the result of *)
(* applying the algorithm to the cube                  *)
let apply_algorithm (alg : algorithm) (c : cube) : cube = 
  List.fold_left (fun cacc t -> move cacc t) c alg

(* Given a scramble, return the result of applying the *)
(* scramble to a solved cube                           *)
let apply_scramble (scr : scramble) : cube = 
  apply_algorithm scr solved_cube

(* ----------------------------------------------------------------------- *)
(* Generating scrambles *)

let gen_scrambles (i : int) (b: bool) : scramble list =
 (* Gets the last element of a list *)
 let getlastelement (lst : 'a list) : 'a = 
   List.nth lst ((List.length lst)-1) in 
 (** Finds the number of individual turns possible after a certain list
  * depending on the boolean argument *)
 let get_possibles_after (tlst:turn list) (b:bool) : turn list =
  if (b || tlst==[]) then [F;F';F2;U;U';U2;R;R';R2] else
  match (getlastelement tlst) with
      | U | U' | U2 -> [R;R';R2;F;F';F2]
      | R | R' | R2 -> [U;U';U2;F;F';F2]
      | F | F' | F2 -> [U;U';U2;R;R';R2] in
 (* Takes a list and returns it with all possible new turns added *)
 let generator (lst: scramble) : scramble list =
  let foo acc ele = (List.rev (ele::(List.rev lst)))::acc in
    List.fold_left foo [] (get_possibles_after lst b) in
 (* Takes a list of scrambles of length n and returns them with length n+1 *)
 let regenerator (lstlst : scramble list) : scramble list =
  let foo acc ele = (generator ele)@acc in
   List.fold_left foo [] lstlst in
 (** Generatres all scrambles of a given length by folding through a list
  * of size, the given length *)
 let recur_regenerate acc ele = regenerator acc in
     List.fold_left recur_regenerate [[]] (get_list i);;

let gen_scramble (i : int) : scramble =
 (* Returns the nth element of the scramble list *)
 let find_nth (lst : scramble list) (i : int) =
  let foo acc ele = if ((fst acc)=i) then ((fst acc)+1,ele) 
   else ((fst acc)+1,(snd acc)) in
   snd(List.fold_left foo (0,[]) lst) in
 (* Generates all the scrambles of given length possible *)
 let scrambles = (gen_scrambles i false) in
 (* Returns the length of the scramble list *)
 let list_length (lst : scramble list) : int =
   List.fold_left (fun acc ele -> acc +1) 0 lst in
 (* Returns a random scramble *)
 find_nth scrambles (Random.int (list_length scrambles));;

(* ----------------------------------------------------------------------- *)
(* Solving using orientation and permutation *)

let gen_inverse_algorithm (a : algorithm) : algorithm=
 (* Function to get inverse of one turn *)
 let get_inverse (t : turn) : turn =
 match t with 
 | R2 | U2 | F2 -> t
 | R' -> R
 | F' -> F
 | U' -> U
 | U -> U'
 | R -> R'
 | F -> F' in
 (* Fold through a list getting the inverse of each turn *)
 let foo acc ele = (get_inverse ele)::acc in
  List.fold_left foo [] a;;

let gen_conjugate_algorithm (setup : algorithm) (alg : algorithm) : algorithm =
 (* Creating a tail recursive algorithm to join two lists*)
 let join (lst1 : algorithm) (lst2 : algorithm) : algorithm =
  (* Works like rev_append by reversing a list *)
  let flipper (lst1 : algorithm) (lst2 : algorithm) : algorithm =
   let foo acc ele = ele::acc in
    List.fold_left foo lst2 lst1 in
  flipper (flipper lst1 []) lst2 in 
 join (join setup alg) (gen_inverse_algorithm setup);;

let orient_cube_alg (c:cube) : algorithm =
 (*Counts the number of triplets of CW/CCW orients in the cube c and its type*)
 let countTrips (c:cube) : (int*orientation) =
  let foo acc ele = if (snd(snd ele)==CCW) then 
   if (fst(acc)+1>0) then (fst(acc)+1,CCW) else (fst(acc)+1,snd(acc)) 
    else if (snd(snd ele)==CW) then 
   if (fst(acc)-1<0) then (fst(acc)-1,CW) else (fst(acc)-1,snd(acc)) 
    else acc in
    let res = List.fold_left foo (0,O) c in
       (abs (fst(res))/3,snd(res)) in
 (* Returns a triplet of pieces with CW or CCW orientations in the cube c *)
 let getTrip (c:cube) : (piece * piece) * piece =
  let checkfor = (snd(countTrips c)) in
   let foo acc ele = if ((snd(snd ele)=checkfor)) 
      then (fst(ele))::acc else acc in
    let lst = List.fold_left foo [] c in
     (((List.nth lst 0),(List.nth lst 1)),List.nth lst 2) in
 (* Correctly orients all the triplets to leave cube with equal C & CCW *)
 let orientTrips (c:cube) : algorithm =
  let foo acc ele = 
   let curr_cube_pos = apply_algorithm acc c in
    let trip = fst(getTrip curr_cube_pos) in
     let gen_conj = gen_conjugate_algorithm in (* name too long *)
     acc@(gen_conj (get_setup_moves (fst(trip)) (snd(trip))) orient_corners) in
       List.fold_left foo [] (get_list (fst(countTrips c))) in
 (* Counts the number of CW-CCW pairs in the cube c *)
 let countCWCCWPair (c:cube) : int=
  let foo acc ele = 
  if (snd(snd ele)==CCW) then (fst(acc),snd(acc)+1) else if (snd(snd ele)==CW) 
   then (fst(acc)+1,snd(acc)) else acc in
    let pair = List.fold_left foo (0,0) c in
     if (fst(pair)<snd(pair)) then fst(pair) else snd(pair) in
 (* Returns a the pieces containing a CW-CCW pair in the cube c *)
 let getPair (c:cube) : (piece * piece) =
  let foo acc ele = 
  if (snd(snd ele)==CCW) then (fst(acc),fst(ele)) else if (snd(snd ele)==CW) 
   then (fst(ele),snd(acc)) else acc in
    List.fold_left foo (DBL,DBL) c in
 (* Orients the CW-CCW pairs correctly in the cube c *) 
 let orient (c:cube) : algorithm =
  let foo acc ele = 
   let curr_cube_pos = apply_algorithm acc c in
    let pair = (getPair curr_cube_pos) in
     let gen_conj = gen_conjugate_algorithm in (* name too long *)
     acc@(gen_conj (get_setup_moves (fst(pair)) (snd(pair))) orient_corners) in
       List.fold_left foo [] (get_list (countCWCCWPair c)) in
 (* Orients the whole cube *)
 orient (apply_algorithm (orientTrips c) c) @ (orientTrips c);;

let permute_cube_alg (c : cube) : algorithm =
 (* Returns the position of piece p in the cube c *)
 let findPosOfPiece (p:piece) (c:cube) : position = 
  let foo = fun acc ele -> if(fst(snd (ele)) = p) then fst(ele) else acc in
   List.fold_left foo DBL c in 
 (* Puts the corner pos1 in the cube c in its correct position *)
 let fixcorner (c:cube) (pos1:piece) : algorithm = 
  if (pos1 = (findPosOfPiece pos1 c) ) then [] else
   let gen_conj = gen_conjugate_algorithm in (* name too long *)
   gen_conj (get_setup_moves pos1 (findPosOfPiece pos1 c)) permute_corners in
 (* Folds through possible corner types and fixes all of them in the cube c *)
 let foo acc ele = 
  let curr_cube_pos = apply_algorithm acc c in
    acc@(fixcorner curr_cube_pos ele) in
   List.fold_left foo [] [UBL;UBR;UFR;UFL;DBL;DBR;DFR;DFL];;

let solve_cube_alg (c:cube) : algorithm =
 (* Finding the algorithm to orient the corners of the cube*)
 let orient_alg = orient_cube_alg c in
 (* Finding the algorithm to position the corners of the cube *)
   orient_alg@(permute_cube_alg (apply_algorithm orient_alg c));;

(* ----------------------------------------------------------------------- *)
(* Solving using 11 moves *)
let semi_opt_alg (c:cube) : algorithm = 
 (* Re-initialize the solved cube *)
 let solved_cube : cube=  
  [(UBL, (UBL,O)); (UBR, (UBR,O)); (UFR, (UFR,O)); (UFL, (UFL,O));
  (DBL, (DBL,O)); (DBR, (DBR,O)); (DFR, (DFR,O)); (DFL, (DFL,O))] in
 (* Generates a hash table of the possible output after 6 random scrambles *)
 let gen_cubes (c:cube) : (cube,algorithm) Hashtbl.t = 
  let fold_helper acc ele = hashtbl_add acc (apply_algorithm ele c) ele in
   List.fold_left fold_helper (make_hashtbl []) (gen_scrambles 6 false) in
 (** Checks all scrambled 5 lengths away from cube c to 
  * return algorithm from initial cube to c *)
 let moveToCube(h:(cube,algorithm) Hashtbl.t) (c:cube) : algorithm= 
  let fold_helper acc ele = if (in_hashtbl h (apply_algorithm ele c)) 
   then (hashtbl_find h (apply_algorithm ele c))@(gen_inverse_algorithm(ele)) 
  else acc in
   List.fold_left fold_helper [] (gen_scrambles 5 false) in
 (* Generates a 11 move combination to move from c to the solved cube *)
 moveToCube (gen_cubes c) solved_cube;;
