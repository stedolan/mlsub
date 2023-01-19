open Exp
open Typedefs
open Tuple_fields

type (_, _) equal = Refl : ('a, 'a) equal

module Type_id = struct
  type (_,_) eq_result = Equal : ('a,'a) eq_result | Not_equal : ('a,'b) eq_result

  type _ tag_impl = ..
  module type Tag = sig type a type _ tag_impl += Tag : a tag_impl end
  type 'a tag = (module Tag with type a = 'a)
  let fresh (type t) () : t tag =
    let module Tag = struct type a = t type _ tag_impl += Tag : t tag_impl end in
    (module Tag)

  let code (type t) ((module M) : t tag) =
    Obj.Extension_constructor.(id (of_val M.Tag))

  let hash (type t) tag = code tag

  let equal (type a) (type b) ((module A) : a tag) ((module B) : b tag) :
    (a, b) eq_result =
    match A.Tag with
    | B.Tag -> Equal
    | _ -> Not_equal

  let to_bool (type a) (type b) : (a, b) eq_result -> bool =
    function
    | Equal -> true
    | Not_equal -> false
    

  let and_eq (type a) (type b)
    (p : (a, b) eq_result)
    (q : (a, b) eq_result) : (a, b) eq_result =
    match p, q with
    | Equal, Equal -> Equal
    | _ -> Not_equal
end

type z = Z and 'a s = S
type 'n count = Z : z count | S : 'n count -> 'n s count
module Clist = struct
  type ('n, 'm, +'a) prefix =
    | [] : ('n, 'n, 'a) prefix
    | (::) : 'a * ('n, 'm, 'a) prefix -> ('n s, 'm, 'a) prefix

  type ('w, +'a) t = ('w, z, 'a) prefix

  type ('m, 'a) unknown_len =
    | Ex : ('n, 'm, 'a) prefix -> ('m, 'a) unknown_len [@@unboxed]

  let refute_pfx (type a) (_ : (a, a s, _) prefix) =
    (* You can actually hit this by using -rectypes or other trickery to make
       a type t = t s, so this has to be a runtime failure *)
    assert false

  let rec of_list : _ list -> (_,_) unknown_len = function
    | [] -> Ex []
    | x :: xs ->
       let Ex xs = of_list xs in
       Ex (x :: xs)

  let rec to_list : type n m . (n, m, _) prefix -> _ list = function
    | [] -> []
    | x :: xs -> x :: to_list xs

  let rec append : type n m w .
    (n, m, _) prefix ->
    (m, w, _) prefix ->
    (n, w, _) prefix =
    fun xs ys ->
    match xs with
    | [] -> ys
    | x :: xs -> x :: (append xs ys)

  let rec map : type n m . ('a -> 'b) -> (n, m, 'a) prefix -> (n, m, 'b) prefix =
    fun f xs ->
    match xs with
    | [] -> []
    | x :: xs ->
       let y = f x in
       let ys = map f xs in
       y :: ys

  let rec split : type n m w .
    (n, m, _) prefix ->
    (m, w, _) prefix ->
    (n, w, 'a) prefix ->
    (n, m, 'a) prefix * (m, w, 'a) prefix =
    fun pfx1 pfx2 xs ->
    match pfx1 with
    | [] ->
       [], xs
    | _ :: pfx1 ->
       begin match xs with
       | [] ->
          refute_pfx (append (map ignore pfx1) (map ignore pfx2))
       | x :: xs ->
          let xs1, xs2 = split pfx1 pfx2 xs in
          x :: xs1, xs2
       end

  let rec zip : type n m .
    (n, m, _) prefix ->
    (n, m, _) prefix ->
    (n, m, _) prefix =
    fun xs ys ->
    match xs, ys with
    | [], [] -> []
    | x :: xs, y :: ys -> (x, y) :: zip xs ys
    | _ -> assert false

  let rec equal : type n m w.
    ('a -> 'a -> bool) ->
    (w, n, 'a) prefix ->
    (w, m, 'a) prefix ->
    (n, m) Type_id.eq_result =
    fun eq x y ->
    match x, y with
    | [], [] -> Equal
    | x :: xs, y :: ys ->
       begin match equal eq xs ys with
       | Equal -> if eq x y then Equal else Not_equal
       | Not_equal -> Not_equal
       end
    | [], _ :: _
    | _ :: _, [] -> Not_equal

  let rec equal' : type n m w.
    ('a -> 'a -> bool) ->
    (n, w, 'a) prefix ->
    (m, w, 'a) prefix ->
    (n, m) Type_id.eq_result =
    fun eq x y ->
    match x, y with
    | [], [] -> Equal
    | x :: xs, y :: ys ->
       begin match equal' eq xs ys with
       | Equal -> if eq x y then Equal else Not_equal
       | Not_equal -> Not_equal
       end
    | [], _ :: _
    | _ :: _, [] -> Not_equal


  let rec compare_lengths : type n m k . (n, k, _) prefix -> (m, k, _) prefix -> (n,m) Type_id.eq_result =
    fun xs ys ->
    match xs, ys with
    | [], [] -> Equal
    | _ :: xs, _ :: ys ->
       begin match compare_lengths xs ys with
       | Equal -> Equal
       | Not_equal -> Not_equal
       end
    | [], _ :: _
    | _ :: _, [] -> Not_equal

  let of_list_length (type n) ~(len : (n,_,_) prefix) xs : (n,_,_) prefix option =
    let Ex xs = of_list xs in
    match compare_lengths len xs with
    | Equal -> Some xs
    | Not_equal -> None
end


type action = {
  rhs: exp;
  id: int;
  bound: (ptyp ref * IR.value IR.Binder.t) SymMap.t;
  mutable used: bool;
}

type bindings = ptyp SymMap.t

type 'w pat_row = ('w, pat) Clist.t * (bindings * action)

type 'w pat_matrix = 'w pat_row list

type 'n dectree =
  { tree: 'n dectree';
    tag: 'n Type_id.tag;
    empty: bool;
    total: bool;
    mutable refcount : int }

and _ dectree' =
  | Done : action -> z dectree'
  | Failure : z dectree'
  | Any : 'n dectree -> 'n s dectree'
  (* Cases: nonempty and sorted *)
  | Cases : (Typedefs.Cons.tuple_tag * 'n fields_split) list -> 'n s dectree'
  | Fields : 'n fields_split -> 'n s dectree'

and 'n fields_split =
  | Proj : ('m, 'n, Tuple_fields.field_name) Clist.prefix * 'm dectree -> 'n fields_split


type packed_dectree' = Packed : 'n dectree' -> packed_dectree'

module DectreeHash = struct
  let equal_dectree (type a) (type b) (a : a dectree) (b : b dectree) : (a, b) Type_id.eq_result =
    let eq = Type_id.equal a.tag b.tag in
    (match eq with
     | Equal -> assert (a == b)
     | Not_equal -> assert (Obj.repr a != Obj.repr b));
    eq

  let equal_fields_split (type a) (type b) (a : a fields_split) (b : b fields_split) :
        (a, b) Type_id.eq_result =
    let Proj (pfxa, a) = a in
    let Proj (pfxb, b) = b in
    match equal_dectree a b with
    | Equal ->
       begin match Clist.equal (Stdlib.(=)) pfxa pfxb with
       | Equal -> Equal
       | Not_equal -> Not_equal
       end
    | Not_equal ->
       Not_equal

  let equal_dectree' (type a) (type b) (a : a dectree') (b : b dectree') : (a, b) Type_id.eq_result =
    match a, b with
    | Done a, Done b ->
       assert ((a.id = b.id) = (a == b));
       if a.id = b.id then Equal else Not_equal
    | Failure, Failure ->
       Equal
    | Any a, Any b ->
       begin match equal_dectree a b with
       | Equal -> Equal
       | Not_equal -> Not_equal
       end
    | Cases a, Cases b ->
       let eq_case (sa, ca) (sb, cb) =
         if String.equal sa sb
         then equal_fields_split ca cb
         else Type_id.Not_equal
       in
       if List.compare_lengths a b <> 0 then Not_equal
       else begin match
         List.fold_left
           (Type_id.and_eq)
           (eq_case (List.hd a) (List.hd b))
           (List.map2 eq_case (List.tl a) (List.tl b))
       with
       | Equal -> Equal
       | Not_equal -> Not_equal
       end
    | Fields a, Fields b ->
       begin match
         equal_fields_split a b
       with
       | Equal -> Equal
       | Not_equal -> Not_equal
       end
    | (Done _ | Failure | Any _ | Cases _ | Fields _), _ -> Not_equal

  type t = packed_dectree'

  let equal (Packed a) (Packed b) =
    match equal_dectree' a b with
    | Equal -> true
    | Not_equal -> false

  let mix h =
    let h = h * 0x43297583 in
    let h = h lxor (h lsr 16) in
    let h = h * 0x85ebca6b in
    let h = h lxor (h lsr 13) in
    let h = h * 0xc2b2ae35 in
    let h = h lxor (h lsr 16) in
    h

  let hash_dectree' a =
    mix (Type_id.hash a.tag)

  let hash_fields (Proj (pfx, t)) =
    List.fold_left
      (fun h fn -> h + Hashtbl.hash fn)
      (hash_dectree' t)
      (Clist.to_list pfx)

  let hash (Packed a) =
    mix @@ match a with
    | Done a ->
       mix 1 + a.id
    | Failure ->
       mix 2
    | Any a ->
       mix 3 + hash_dectree' a
    | Cases cases ->
       List.fold_left (fun h (s, fs) ->
         h + Hashtbl.hash s + hash_fields fs) (mix 4) cases
    | Fields fs ->
       mix 5 + hash_fields fs
end

module Hashcons = struct
  module Tbl = Hashtbl.Make (DectreeHash)
  type packed_kv =
    | Packed : 'w dectree' * 'w dectree -> packed_kv
  type t = packed_kv Tbl.t
  let fresh_table () : t = Tbl.create 20

  let is_empty (type a) : a dectree' -> bool = function
    | Done _ -> false
    | Failure -> true
    | Any t -> t.empty
    | Cases cases -> List.for_all (fun (_, Proj (_, fs)) -> fs.empty) cases
    | Fields (Proj (_, fs)) -> fs.empty

  let is_total (type a) : a dectree' -> bool = function
    | Done _ -> true
    | Failure -> false
    | Any t -> t.total
    | Cases cases -> List.for_all (fun (_, Proj (_, fs)) -> fs.total) cases
    | Fields (Proj (_, fs)) -> fs.total

  let mk tbl (type n) (t : n dectree') : n dectree =
    match Tbl.find tbl (Packed t) with
    | Packed (t', res) ->
       begin match DectreeHash.equal_dectree' t t' with
       | Equal -> res.refcount <- res.refcount + 1; res
       | Not_equal -> assert false
       end
    | exception Not_found ->
       let res =
         { tree = t;
           tag = Type_id.fresh ();
           empty = is_empty t;
           total = is_total t;
           refcount = 1 }
       in
       Tbl.add tbl (Packed t) (Packed (t, res));
       res
end


type pat_head =
  | Hany
  | Hcase of Cons.tuple_tag * pat tuple_fields
  | Hfields of pat tuple_fields

type 'w peeled_row =
  { head: pat_head;
    head_loc: Location.t;
    var: symbol option;
    rest: 'w pat_row }

let rec peel_pat_heads :
  type w . w s pat_matrix -> w peeled_row list
  = function
  | [] -> []
  | (((None,loc) :: _ps), _act) :: _rest ->
     Error.fail loc Syntax
  | (((Some p,head_loc) :: ps), act) :: rest ->
     match p with
     | Pparens p ->
        peel_pat_heads (((p :: ps), act) :: rest)
     | Por (p, q) ->
        peel_pat_heads (((p :: ps), act) :: ((q :: ps), act) :: rest)
     | Pany ->
        {head=Hany; head_loc; var=None; rest=(ps, act)} ::
        peel_pat_heads rest
     | Pvar (v,_) ->
        {head=Hany; head_loc; var=Some v; rest = (ps, act)} ::
        peel_pat_heads rest
     | Ptuple (None, fields) ->
        {head=Hfields fields; head_loc; var=None; rest= (ps, act)} ::
        peel_pat_heads rest
     | Ptuple (Some (tag, _), fields) ->
        {head=Hcase (tag, fields); head_loc; var=None; rest= (ps, act)} ::
        peel_pat_heads rest

type split_kind =
  | Sany
  | Scases of ptyp tuple_fields SymMap.t
  | Sfields of ptyp tuple_fields

let join_pat_conses cons_locs =
  let rec aux = function
    | [] -> assert false
    | [cons, _loc] ->
       Cons.map_one ~neg:(fun _ -> ()) ~pos:(fun _ -> ()) cons
    | (cons, loc) :: rest ->
       let cons' = aux rest in
       if not (Cons.compatible cons cons') then begin
         let loc' =
           List.find_map (fun (cons', loc') -> if Cons.compatible cons cons' then None else Some loc') rest
           |> Option.value ~default:Location.noloc in
         Error.fail loc (Incompatible_patterns loc')
       end;
       let cons = Cons.join_head_one cons cons' in
       Cons.map_one ~neg:(fun _ -> ()) ~pos:(fun _ -> ()) cons
  in
  aux cons_locs

(* Decide the split kind that we are going to check the patterns with. *)
let decide_split_kind ~matchloc env (ty : ptyp) (heads : _ peeled_row list) =
  if List.for_all (function {head=Hany;_} -> true | _ -> false) heads then
    (* If there are no destructuring patterns, any type will do *)
    Sany
  else if List.for_all (function {head=Hany | Hfields _;_} -> true | {head=Hcase _;_} -> false) heads then
    (* All product field constructors *)
    let fields =
      List.concat_map (fun {head; head_loc; _} ->
        match head with
        | Hany -> []
        | Hcase _ -> assert false
        | Hfields fs -> [Cons.Record(None, fs), head_loc])
        heads
      |> join_pat_conses
    in
    match
      Types.match_typ env ty (Location.noloc (*FIXME*)) fields
    with
    | Ok (Record (_, fs)) -> Sfields (map_fields (fun _fn ((),ty) -> ty) fs)
    | Ok _ -> assert false
    | Error e -> Error.fail matchloc (Conflict (`Pat, e))
  else match ty with
  | Tcons {conses;_}
       when List.for_all (function Cons.Record (Some _, _) -> true | _ -> false) conses ->
     let cases =
       conses
       |> List.map (function
         | Cons.Record (Some tag, fields) -> tag, fields
         | _ -> assert false)
       |> List.to_seq
       |> SymMap.of_seq
     in
     Scases cases
  | _ ->
     let inferred_cases =
       List.fold_left (fun acc row ->
         match row.head with
         | Hany | Hfields _ ->
            Error.fail row.head_loc (Illformed_pat `Unknown_cases)
         | Hcase (tag, fields) ->
            let cons = Cons.Record(Some tag, fields) in
            let prev =
              try SymMap.find tag acc
              with Not_found -> []
            in
            SymMap.add tag ((cons,row.head_loc) :: prev) acc)
         SymMap.empty
         heads
       |> SymMap.map join_pat_conses
     in
     let loc = List.concat_map (fun row -> row.head_loc) heads in
     let inferred_cases =
       SymMap.map (Cons.map_one ~neg:(fun _ -> assert false) ~pos:(fun () -> ref (Tcons Cons.bottom))) inferred_cases in
     let cons =
       Cons.make' ~loc (SymMap.fold (fun _tag fields acc -> fields :: acc) inferred_cases [])
     in
     begin match Types.match_typ2 env ty cons with
     | Ok () -> ()
     | Error e -> Error.fail matchloc (Conflict (`Pat, e))
     end;
     Scases (SymMap.map (function
                 | Cons.Record (_, fs) -> map_fields (fun _fn r -> !r) fs
                 | _ -> assert false) inferred_cases)

let any : pat = (Some Pany, noloc)

(* FIXME as patterns here *)
let read_fields :
  type n m . tag:string option -> (m, n, field_name) Clist.prefix -> n peeled_row -> m pat_row =
  fun ~tag fields {head; head_loc=_; var=_; rest=(row, act)} ->
  match head with
  | Hany ->
     Clist.append (Clist.map (fun _ -> any) fields) row, act
  | Hcase (_, fs)
  | Hfields fs ->
     begin match head, tag with
     | Hcase (tag', _), Some tag -> assert (String.equal tag tag')
     | Hcase (_, _), None -> assert false
     | _ -> ()
     end;
     let lookup fn =
       match get_field_opt fs fn with
       | Some pat -> pat
       | None -> failwith "missing!"
     in
     Clist.append (Clist.map lookup fields) row, act

let matches_tag tag row =
  match row.head with
  | Hany -> true
  | Hfields _ -> true
  | Hcase (tag', _) -> String.equal tag tag'

let row_tail typ row =
  match row.var, row.rest with
  | None, rest -> rest
  | Some v, (pats, (bindings, act)) ->
     (pats, (SymMap.add v typ bindings, act))


let rec split_cases :
  type w . table:_ -> matchloc:_ -> _ -> _ -> (w, ptyp) Clist.t -> w pat_matrix -> w dectree =
  fun ~table ~matchloc env vars typs mat ->
  match typs with
  | [] ->
     begin match mat with
     | [] ->
        Hashcons.mk table Failure
     | ([], (bindings, act)) :: _ ->
        act.used <- true;
        bindings |> SymMap.iter (fun v typ ->
          let (r, _) = SymMap.find v act.bound in
          r := Types.join_ptyp env !r typ);
        Hashcons.mk table (Done act)
     end

  | typ :: typs ->
     let split_fields ~tag fs mat =
        let Ex fs = Clist.of_list (list_fields fs) in
        let field_names = Clist.map fst fs in
        let field_types = Clist.map snd fs in
        let mat = List.map (read_fields ~tag field_names) mat in
        let rest =
          split_cases ~table ~matchloc env vars (Clist.append field_types typs) mat in
        Proj (field_names, rest)
     in

     let mat = peel_pat_heads mat in
       
     match decide_split_kind ~matchloc env typ mat with
     | Sany ->
        let rest = split_cases ~table ~matchloc env vars typs (List.map (row_tail typ) mat) in
        Hashcons.mk table (Any rest)
     | Sfields fs ->
        let fs = split_fields ~tag:None fs mat in
        Hashcons.mk table (Fields fs)
     | Scases cases ->
        let cases = SymMap.mapi (fun tag fs ->
          let mat = List.filter (matches_tag tag) mat in
          split_fields ~tag:(Some tag) fs mat) cases in
        let cases = SymMap.to_seq cases |> List.of_seq in
        Hashcons.mk table (Cases cases)

module Memo_table(X : sig type !_ input type 'a t constraint 'a = _ input end) = struct
  include X
  type wpacked = Packed : 'w dectree * 'w X.t -> wpacked

  module Tbl = Hashtbl.Make (struct
    type t = int
    let equal = Int.equal
    let hash = Hashtbl.hash
  end)
  type t = wpacked Tbl.t
  let fresh () : t = Tbl.create 20

  let memoize (type w) (type a) (table : t) (f : w X.input dectree' -> w X.input X.t) (x : w X.input dectree) : w X.input X.t =
    let id = Type_id.code x.tag in
    match Tbl.find table id with
    | Packed (x', v) ->
       begin match Type_id.equal x.tag x'.tag with
       | Not_equal -> assert false
       | Equal -> assert (x == x'); v
       end
    | exception Not_found ->
       let r = f x.tree in
       Tbl.add table id (Packed (x, r));
       r

  type memoized = { f : 'a. 'a X.input dectree -> 'a X.input X.t }
end

let find_map_unique ~equal f xs =
  let rec aux u = function
    | [] -> Some u
    | x :: xs ->
       begin match f x with
       | Some u' when equal u u' -> aux u xs
       | _ -> None
       end
  in
  match xs with
  | [] ->
     invalid_arg "find_map_unique: empty list"
  | x :: xs ->
     match f x with
     | None -> None
     | Some u -> aux u xs

module Dectree_tails_tag = struct
  type 'a input = 'a s
  type 'ws t = 'w dectree option constraint 'ws = 'w s
end
let dectree_tails () : Memo_table(Dectree_tails_tag).memoized =
  let module Memo_table = Memo_table (Dectree_tails_tag) in
  let table = Memo_table.fresh () in
  let unique_dt f xs =
    find_map_unique ~equal:(fun a b -> DectreeHash.equal_dectree a b |> Type_id.to_bool) f xs in

  let rec dectree_tails : type w . w s dectree' -> w dectree option =
    function
    | Any tail ->
       Some tail
    | Cases cases ->
       cases |> unique_dt (fun (_, fs) -> dectree_fields_tails fs)
    | Fields fs ->
       dectree_fields_tails fs
  
  and dectree_fields_tails : type n . n fields_split -> n dectree option =
    fun (Proj (fs, t)) ->
    let rec aux : type m . (m, n, field_name) Clist.prefix -> m dectree -> n dectree option =
      fun pfx t ->
      match pfx with
      | [] -> Some t
      | _ :: fs ->
         let ans = Memo_table.memoize table dectree_tails t in
         match ans with
         | None -> None
         | Some t -> aux fs t
    in
    aux fs t
  in
  { f = fun t -> Memo_table.memoize table dectree_tails t }

module Dectree_heads_tag = struct
  type 'n head_dectree = Chopped : ('k, 'n, _) Clist.prefix * ('k dectree) -> 'n head_dectree
  type (_,_) tag = T : ('n, 'n head_dectree) tag
  type fn = { f : 'k 'n 'a . ('k, 'n, 'a) Clist.prefix -> 'n dectree -> 'k dectree }
end
(*
let dectree_head () : Dectree_heads_tag.fn =
  let module Memo_table = Memo_table (Dectree_heads_tag) in
  let table = Memo_table.fresh () in
  let rec dectree_head : type k n . (k, n, _) Clist.prefix -> n dectree -> k dectree =
    fun pfx dt ->
    let Chopped (pfx', t') = dectree_head' dt in
    
  and dectree_head' : type n . n dectree -> n Dectree_heads_tag.head_dectree =
    asdf
  in
  { f = dectree_head }
*)
(*
let rec dectree_head : type k n . (n, k, _) Clist.prefix -> n dectree -> k dectree =
  fun pfx dt ->
  match pfx, dt with
  | [], dt -> dt
  | _::pfx, Any dt ->
     let h = dectree_head pfx dt.dectree in
     Any h
  | _::pfx, Cases cases -> asdf
  | _::pfx, Fields fs -> asdf
*)
(*
let counterexamples t =
  let dectree_tails = dectree_tails () in
  let unmatched_fields :
    type n m . tag:string option -> (m, n, field_name) Clist.prefix ->
      (m, pat) Clist.t -> (n s, pat) Clist.t =
    fun ~tag fields unmatched ->
    let fs, rest = Clist.split fields unmatched in
    let fields =
      Clist.zip fields fs
      |> Clist.to_list
      |> Tuple_fields.fields_of_list ~fopen:`Closed(*FIXME*)
    in
    let pat =
      Ptuple (Option.map (fun s -> s, Location.noloc) tag, fields)
    in
    (Some pat, Location.noloc) :: rest
  in
  
  let rec counterexamples :
    type w . w dectree -> (w, pat) Clist.t list =
    function
    | Done _ -> []
    | Failure -> [[]]
    | Any t ->
       let unmatched = counterexamples t.dectree in
       List.map (fun ps -> Clist.(any :: ps)) unmatched
    | Cases cases ->
       cases |> List.concat_map (fun (tag, (Proj (names, t))) ->
         List.map (unmatched_fields ~tag:(Some tag) names) (counterexamples t.dectree))
    | Fields (Proj (names, t')) as t ->
       begin match dectree_tails.f T t with
       | None ->
          List.map (unmatched_fields ~tag:None names) (counterexamples t'.dectree)
       | Some tail ->
          let tail = counterexamples tail.dectree in
          asdf
       end
  in
  counterexamples t
*)
let counterexamples depth t =
  let dectree_tails = dectree_tails () in
  let unmatched_fields :
    type n m k . tag:string option -> (m, n, field_name) Clist.prefix -> (n, k, _) Clist.prefix ->
      (m, k, pat) Clist.prefix -> (n s, k, pat) Clist.prefix =
    fun ~tag fields pfx unmatched ->
    let fs, rest = Clist.split fields pfx unmatched in
    let fields =
      Clist.zip fields fs
      |> Clist.to_list
      |> Tuple_fields.fields_of_list ~fopen:`Closed(*FIXME*)
    in
    let pat =
      Ptuple (Option.map (fun s -> s, Location.noloc) tag, fields)
    in
    (Some pat, Location.noloc) :: rest
  in
  
  let rec examples :
    type n k . sense:bool -> (n, k, _) Clist.prefix -> n dectree -> (n, k, pat) Clist.prefix list =
    fun ~sense pfx dt ->
    match sense, dt with
    | true, { empty = true; _ }
    | false, { total = true; _ } ->
       (* No examples / counterexamples *)
       []
    | true, { total = true; _ }
    | false, { empty = true; _ } ->
       (* Everything is an example / counterexample *)
       [ Clist.map (fun _ -> any) pfx ]
    | _, { total = false; empty = false; _ } ->
       match pfx with
       | [] -> [ [] ]
       | _ :: pfx ->
          match dectree_tails.f dt with
          | Some tail ->
             (* Separable decision tree (all tails agree) *)
             let ex_head = examples ~sense [()] dt in
             let ex_tail = examples ~sense pfx tail in
             assert false
          | None ->
             match dt.tree with
             | Any dt ->
                let ex = examples ~sense pfx dt in
                 List.map (fun ps -> Clist.(any :: ps)) ex
             | Cases cases ->
                cases |> List.concat_map (fun (tag, (Proj (names, t))) ->
                  List.map (unmatched_fields ~tag:(Some tag) names pfx)
                    (examples ~sense (Clist.append (Clist.map ignore names) pfx) t))
             | Fields (Proj (names, t')) ->
                let ex = examples ~sense (Clist.append (Clist.map ignore names) pfx) t' in
                List.map (unmatched_fields ~tag:None names pfx) ex
  in
  examples ~sense:false depth t


(*
 * Parse a list of cases into a pattern matrix
 *)

let check_equ_fvs loc p q =
  SymMap.merge (fun k l r ->
   match l, r with
   | None, None -> None
   | Some _ as x, Some _ -> x
   | None, Some _
   | Some _, None ->
      Error.fail loc (Illformed_pat (`Orpat_different_names k)))
  p q

let rec check_fvs_list ps =
  let acc_pat acc p =
    let fvs = check_fvs p in
    SymMap.merge (fun k l r ->
      match l, r with
      | None, None -> None
      | (Some _ as x), None
      | None, (Some _ as x) -> x
      | Some aloc, Some bloc ->
         Error.fail bloc (Illformed_pat (`Duplicate_name (k,aloc))))
      acc fvs
  in
  List.fold_left acc_pat SymMap.empty ps
and check_fvs = function
  | None, _ -> SymMap.empty
  | Some p, loc -> check_fvs' loc p
and check_fvs' ploc = function
  | Pany ->
     SymMap.empty
  | Pvar (v, _) ->
     SymMap.singleton v ploc
  | Ptuple (_, fs) ->
     check_fvs_list (List.map snd (list_fields fs))
  | Pparens p ->
     check_fvs p
  | Por (p, q) ->
     let p = check_fvs p in
     let q = check_fvs q in
     check_equ_fvs ploc p q

let check_fvs_mat loc = function
  | [] -> assert false
  | ps :: pps ->
     List.fold_left (check_equ_fvs loc)
       (check_fvs_list ps)
       (List.map check_fvs_list pps)
  

type ex_split = Ex : 'n dectree -> ex_split
let split_cases ~matchloc env (typs : ptyp list) (cases : case list) =
  let actions =
    cases |> List.mapi (fun id (pps, exp) ->
      let fvs = check_fvs_mat matchloc pps in
      { rhs = exp;
        id;
        bound = SymMap.map (fun _loc -> ref (Tcons Cons.bottom), fst (IR.Binder.fresh ())) fvs;
        used = false })
  in
  let Ex typs = Clist.of_list typs in
  let mat =
    List.map2 (fun (pps, _) b -> pps, b) cases actions
    |> List.concat_map (fun (pps, act) ->
      pps |> List.map (fun ps ->
        match Clist.of_list_length ~len:typs ps with
        | None -> failwith (*FIXME*)  "wrong length of pat row"
        | Some ps -> ps, (SymMap.empty, act)))
  in
  let table = Hashcons.fresh_table () in
  let dtree =
    split_cases ~table ~matchloc env SymMap.empty typs mat in
  let unmatched = counterexamples (Clist.map ignore typs) dtree in 
  let unmatched = List.map Clist.to_list unmatched in
  actions, Ex dtree, unmatched
