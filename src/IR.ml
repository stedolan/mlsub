
module TF = Tuple_fields

module Binder : sig
  type 'a t
  type 'a ref

  val ref : 'a t -> 'a ref
  val name : 'a t -> string option

  val fresh : ?name:string -> unit -> 'a t

  type (_,_) phase
  val phase : unit -> ('p, 'a) phase
  val with_binder : ('p,'a) phase -> 'a t -> 'p -> (unit -> 'r) -> 'r
  val with_binders : ('p, 'a) phase -> ('a t * 'p) list -> (unit -> 'r) -> 'r
  val with_field_binders : ('p, 'a) phase -> ('a t * 'p) TF.tuple_fields -> (unit -> 'r) -> 'r
  val deref : ('p,'a) phase -> 'a ref -> 'p
end = struct
  type _ phase_tag = ..
  type _ phase_tag += Idle

  module type Phase = sig
    type p
    type a
    type _ phase_tag += P : p -> a phase_tag
  end
  type ('p, 'a) phase = (module Phase with type p = 'p and type a = 'a) 

  type 'a cell = { mutable entry : 'a phase_tag; name : string option }
  type 'a t = 'a cell
  type 'a ref = 'a cell

  let name x = x.name
  let ref x = x

  let fresh ?name () =
    { entry = Idle; name }

  let phase (type p) (type a) () : (p, a) phase =
    let module M = struct
      type nonrec p = p
      type nonrec a = a
      type _ phase_tag += P : p -> a phase_tag
    end in
    (module M)

  let with_binder (type p) (type a) ((module P) : (p,a) phase) (cell : a cell) x f =
    (match cell.entry with
     | Idle -> ()
     | _ -> invalid_arg "mutiple uses of binder");
    cell.entry <- P.P x;
    Fun.protect f ~finally:(fun () ->
      cell.entry <- Idle)

  let rec with_binders p binders f =
    match binders with
    | [] -> f ()
    | (b,x) :: rest ->
       with_binder p b x (fun () -> with_binders p rest f)

  let with_field_binders p binders f =
    let binders =
      List.rev (TF.fold_fields (fun acc _ x -> x :: acc) [] binders) in
    with_binders p binders f

  let deref (type p) (type a) ((module P) : (p,a) phase) cell =
    match cell.entry with
    | P.P x -> x
    | Idle -> invalid_arg (Printf.sprintf "deref outside with_binder of %s" (Option.value ~default:"_" cell.name))
    | _ -> invalid_arg (Printf.sprintf "incorrect binder of %s" (Option.value ~default:"_" cell.name))
end

module Symbol : sig
  type t [@@immediate]
  val of_string : string -> t
  val to_string : t -> string
end = struct
  type t = int
  let table = Hashtbl.create 20
  let strings = ref [| "" |]
  let next_id = ref 0

  let of_string s =
    match Hashtbl.find table s with
    | n -> n
    | exception Not_found ->
       let n = !next_id in
       incr next_id;
       if n >= Array.length !strings then
         strings := Array.concat [!strings;!strings];
       (!strings).(n) <- s;
       n

  let to_string n =
    assert (0 <= n && n < !next_id);
    (!strings).(n)
end

(* Based-ish on CBPV, with additional restrictions on functions.
   (CBPV commits to push-enter rather than eval-apply, by allowing
    functions to e.g. do pattern matching between arguments).

   Then I added continuation binding. Now a comp yields no value.

 *)

type tag = Symbol.t
type field = TF.field_name

type cont = [`Cont]

type value =
  | Literal of Exp.literal
  | Var of value Binder.ref
  | Tuple of tag option * value TF.tuple_fields
  | Lambda of value Binder.t TF.tuple_fields * cont Binder.t * comp

and comp =
  | LetVal of value Binder.t * value * comp
  | LetCont of cont Binder.t * value Binder.t list * comp * comp

  | Jump of cont Binder.ref * value list
  | Match of value * (tag * unpacking_cont) list
  | Project of value * unpacking_cont
  | Apply of callee * value TF.tuple_fields * value Binder.t list * comp
  | Trap of string

and unpacking_cont =
  (field * value Binder.t) list * comp

and callee = Func of value | Prim of string

let var v = Var (Binder.ref v)
let jump k vs = Jump (Binder.ref k, vs)

(* Check that cont arities match and binders are well-scoped *)
let wf orig_c =
  let next_lambda = ref 0 in
  let lambda_level () = incr next_lambda; !next_lambda in
  let pval = Binder.phase () and pcont = Binder.phase () in
  let rec value = function
    | Literal _ -> ()
    | Var v -> Binder.deref pval v
    | Tuple (_, vs) -> TF.iter_fields (fun _fn v -> value v) vs
    | Lambda (params, ret, body) ->
       Binder.with_field_binders pval (TF.map_fields (fun _ p -> p, ()) params) @@ fun () ->
         Binder.with_binder pcont ret 1 @@ fun () ->
           comp (lambda_level ()) body
  and unpacking_cont lam (fields, c) =
    Binder.with_binders pval (List.map (fun (_,v) -> v, ()) fields) @@ fun () ->
      comp lam c
  and comp lam = function
    | LetVal (x, v, body) ->
       value v;
       Binder.with_binder pval x () (fun () -> comp lam body)
    | LetCont (k, params, c, body) ->
       let arity = List.length params in
       Binder.with_binders pval (List.map (fun v -> v, ()) params) (fun () -> comp lam c);
       Binder.with_binder pcont k arity (fun () -> comp lam body)
    | Jump (k, args) ->
       let arity = Binder.deref pcont k in
       assert (List.length args = arity);
       List.iter value args
    | Match (v, cases) ->
       value v;
       cases |> List.iter (fun (_tag, c) -> unpacking_cont lam c);
    | Project (v, c) ->
       value v;
       unpacking_cont lam c
    | Apply (v, args, ret, c) ->
       begin match v with Func v -> value v | Prim _ -> () end;
       TF.iter_fields (fun _fn v -> value v) args;
       Binder.with_binders pval (List.map (fun v -> v, ()) ret) (fun () -> comp lam c);
       begin match v with Func _ -> assert (List.length ret = 1) | Prim _ -> () end;
    | Trap _ -> ()
  in
  comp 0 orig_c

(* Print *)
module StrSet = Set.Make (struct type t = string let compare = String.compare end)
let pp origc =
  let vname = Binder.phase () and cname = Binder.phase () in
  let deref ph x =
    match Binder.deref ph x with
    | s -> s
    | exception _ -> "<err>"
  in
  let fresh env name =
    let rec aux i =
      let s = (Printf.sprintf "%s%d" name i) in
      if not (StrSet.mem s env) then s else aux (i+1)
    in
    let name = if not (StrSet.mem name env) then name else aux 2 in
    name, StrSet.add name env
  in

  let fresh_binder ~defname ph env binder f =
    let name = Option.value (Binder.name binder) ~default:defname in
    let name, env = fresh env name in
    Binder.with_binder ph binder name (fun () -> f name env)
  in

  let fresh_binder_list ~defname ph env binders f =
    let rec aux acc env = function
      | b :: rest ->
         fresh_binder ~defname ph env b (fun vn env ->
           aux (vn :: acc) env rest)
      | [] ->
         f (List.rev acc) env
    in
    aux [] env binders
  in

  let open Util.PPFmt in
  let field_name = function
    | TF.Field_positional n -> Printf.sprintf "%d" n
    | TF.Field_named s -> Printf.sprintf "%s" s
  in
  let pp_field_name () s = pp "%s" (field_name s) in
  let pp_fields ppx () xs =
    xs
    |> TF.list_fields
    |> PPrint.separate_map (pp ",@ ") (fun (fn, x) -> pp "@[%a: %a@]" pp_field_name fn ppx x)
  in

  let rec value env () = function
    | Literal (Int n) ->
       pp "%d" n
    | Literal (String s) ->
       pp "\"%s\"" (String.escaped s)
    | Literal (Bool true) ->
       pp "<true>"
    | Literal (Bool false) ->
       pp "<false>"
    | Var v ->
       pp "%s" (deref vname v)
    | Tuple (None, fields) ->
       pp "@,@[(%a)@]" (pp_fields (value env)) fields
    | Tuple (Some tag, fields) ->
       pp "@[%s(%a)@]" (Symbol.to_string tag) (pp_fields (value env)) fields
    | Lambda (params, kret, body) ->
       let ret, env = fresh env "ret" in
       let params = TF.list_fields params in
       let param_names, env =
         List.fold_left (fun (acc, env) (fn, param) ->
           let name = Option.value (Binder.name param) ~default:(field_name fn) in
           let n, env = fresh env name in
           (param, n) :: acc, env) ([], env) params in
       let param_names = List.rev param_names in
       let body =
         Binder.with_binders vname param_names @@ fun () ->
           Binder.with_binder cname kret ret @@ fun () ->
             comp env () body in
       pp "fun @[(%a)@] %s {%a@ }"
         (fun () d -> d) (PPrint.separate_map (pp ",@ ") (fun (_,n) -> pp "%s" n) param_names)
         ret
         (fun () d -> d) (PPrint.(nest 2 (break 1 ^^ body)))

  and comp env () = function
    | LetVal (v, e, body) ->
       let vn, body = fresh_binder ~defname:"x" vname env v (fun vn env -> vn, comp env () body) in
       pp "let %s =@[<2>@ %a@];@ %a" vn (value env) e (fun () d -> d) body
    | LetCont (v, params, kbody, body) ->
       let vn, body = fresh_binder ~defname:"k" cname env v (fun vn env -> vn, comp env () body) in
          let vns, kbody = fresh_binder_list ~defname:"x" vname env params (fun vns env -> vns, comp env () kbody) in
          pp "let %s(@[%a@]) = {%a@ };@ %a"
            vn
            (fun () d -> d) (PPrint.separate_map (pp ",@ ") (fun v -> pp "%s" v) vns)
            (fun () d -> d) (PPrint.(nest 2 (break 1 ^^ kbody)))
            (fun () d -> d) body
    | Jump (k, vs) ->
       pp "%s(@[%a@])"
         (deref cname k)
         (fun () d -> d) (PPrint.separate_map (pp ",@ ") (value env ()) vs)
    | Match (v, cases) ->
       let pcase = function
         | (tag, (fields, body)) ->
            let vars, body = fresh_binder_list ~defname:"x" vname env (List.map snd fields) (fun vns env -> vns, comp env () body) in
            pp "%s(%a) -> {%a@ }"
              (Symbol.to_string tag)
              (fun () d -> d)
              (PPrint.separate_map (pp ",@ ") (fun (f, v) -> pp "%s: %s" (field_name f) v) (List.map2 (fun (a,_) b -> a,b) fields vars)) 
              (fun () d -> d)
              (PPrint.(nest 2 (break 1 ^^ body)))
       in
       pp "match @[%a@] {%a@ }" (value env) v (fun () d -> d) PPrint.(nest 2 (break 1 ^^ separate_map (pp ";@ ") pcase cases))
    | Project (v, (fields, body)) ->
       let vns, body = fresh_binder_list ~defname:"x" vname env (List.map snd fields) (fun vns env -> vns, comp env () body) in
       pp "let @[%a@] = @[%a.(%a)@];@ %a"
         (fun () d -> d) (PPrint.separate_map (pp ",@ ") (fun v -> pp "%s" v) vns)
         (value env) v
         (fun () d -> d) (PPrint.separate_map (pp ",@ ") (fun (v,_) -> pp "%s" (field_name v)) fields)
         (fun () d -> d) body
    | Apply (f, args, ret, body) ->
       let f = match f with Func v -> value env () v | Prim s -> pp "%%%s" s in
       let vns, body = fresh_binder_list ~defname:"x" vname env ret (fun vns env -> vns, comp env () body) in
       pp "let @[%a@] = %a@[(%a)@];@ %a"
         (fun () d -> d) (PPrint.separate_map (pp ",@ ") (fun v -> pp "%s" v) vns)
         (fun () d -> d) f
         (pp_fields (value env)) args
         (fun () d -> d) body
    | Trap s ->
       pp "%s" s
  in
  comp StrSet.empty () origc

(* Substitute away trivial aliases *)
let subst_aliases origc =
  let substv : (value, value) Binder.phase = Binder.phase () in
  let substk : (value list -> comp, cont) Binder.phase = Binder.phase () in

  let is_trivial = function
    | Literal _ -> true
    | Var _ -> true
    | Tuple _ | Lambda _ -> false
  in
  let is_trivial_comp = function
    | Jump (k, vs) when List.for_all is_trivial vs -> Some(k, vs)
    | _ -> None
  in

  let rec value = function
    | Literal _ as v -> v
    | Var v -> Binder.deref substv v
    | Tuple (tag, vs) -> Tuple (tag, TF.map_fields (fun _fn v -> value v) vs)
    | Lambda (params, ret, body) ->
       Lambda (params, ret,
         Binder.with_field_binders substv (TF.map_fields (fun _ p -> p, Var (Binder.ref p)) params) @@ fun () ->
           Binder.with_binder substk ret (fun v -> jump ret v) @@ fun () ->
             comp body)
  and comp = function
    | LetVal (x, v, body) ->
       let v = value v in
       if is_trivial v then
         Binder.with_binder substv x v @@ fun () -> comp body
       else
         LetVal(x, v,
                Binder.with_binder substv x (Var (Binder.ref x)) (fun () -> comp body))
    | LetCont (x, params, k, body) ->
       let k =
         Binder.with_binders substv (List.map (fun p -> p, var p) params) (fun () -> comp k)
       in
       begin match is_trivial_comp k with
       | Some (k, vs) ->
          let sub vs' =
            Binder.with_binders substv (List.map2 (fun a b -> a,b) params vs') @@ fun () ->
              Jump(k, List.map value vs)
          in
          Binder.with_binder substk x sub @@ fun () -> comp body
       | None ->
         LetCont(x, params, k,
                 Binder.with_binder substk x (fun vs -> jump x vs) (fun () -> comp body))
       end
    | Jump (k, args) ->
       (Binder.deref substk k) (List.map value args)
    | Match (v, cases) ->
       Match
         (value v,
          List.map (fun (t, c) -> t, unpacking_cont c) cases)
    | Project (v, fields) ->
       Project (value v, unpacking_cont fields)
    | Apply (f, args, ret, k) ->
       let f = match f with Func f -> Func (value f) | Prim _ as s -> s in
       Apply (f, TF.map_fields (fun _fn v -> value v) args,
              ret,
              Binder.with_binders substv (List.map (fun v -> v, var v) ret) (fun () -> comp k))
    | Trap s -> Trap s

  and unpacking_cont (fields, k) : unpacking_cont =
    (fields,
     Binder.with_binders substv (List.map (fun (_,v) -> v, var v) fields) (fun () -> comp k))

  in
  wf origc;
  let res = comp origc in
  wf res;
  res



(*

(* Substitute away values and continuations used only once *)
let subst1 origc =
  let countv = Binder.phase () and countc = Binder.phase () in
  let substv = Binder.phase () and substc = Binder.phase () in
  let rec value = function
    | Literal _ as v -> fun () -> v
    | Var v ->
       incr (Binder.deref countv v);
       fun () ->
       Binder.deref substv v
    | Tuple (tag, vs) ->
       let vs = TF.map_fields (fun _fn v -> value v) vs in
       fun () ->
       Tuple (tag, TF.map_fields (fun _fn v -> v ()) vs)
    | Lambda (params, ret, body) ->
       let body =
         Binder.with_field_binders countv (TF.map_fields (fun _ p -> p, ref 0) params) @@ fun () ->
           Binder.with_binder countc ret (ref 0) @@ fun () ->
             comp body
       in
       fun () ->
       let body = body () in
       Lambda (params, ret, body)
    and cont = function
      | Named k ->
         incr (Binder.deref countc k);
         fun () ->
         Binder.deref substc k
      | Cont (params, body) ->
         let body =
           Binder.with_binders countv (List.map (fun p -> p, ref 0) params) @@ fun () ->
             comp body
         in
         fun () ->
         let body = body () in
         Cont (params, body)
    and comp = function
      | LetVal (x, e, body) ->
         let e = value e in
         let count = ref 0 in
         let body =
           Binder.with_binder countv x count (fun () -> comp body) in
         fun () ->
         if !count = 0 then
           body ()
         else if !count = 1 then
           let e = e () in
           let body =
             Binder.with_binder substv x e (fun () -> body ()) in
           body
         else
           let e = e () in
           let body =
             Binder.with_binder substv x (Var (Binder.ref x)) (fun () -> body ()) in
           LetVal(x, e, body)

      | LetCont (x, k, body) ->
         let count = ref 0 in
         let k = cont k in
         let body = Binder.with_binder countc x count (fun () -> comp body) in
         fun () ->
         if !count = 0 then
           body ()
         else if !count = 1 then
           let k = k () in
           let body =
             Binder.with_binder substc x k (fun () -> body ()) in
           body
         else
           let k = k () in
           let body = Binder.with_binder substc x (Named (Binder.ref x)) (fun () -> body ()) in
           LetCont(x, k, body)

         

      | _ -> assert false
  in
  comp origc
*)


(* Env on the way down.
   - values: definitions
   - continuations: uses *)
type env = |

(* Env on the way up.
   - values: uses
   - continuations: definitions *)
type cont_env = |

(*

Downward pass:
Keep env with abstraction of values (i.e. optional definitions)
Distinguish known information (match refinement) from constructed values
(Maybe I do need projections?)

Contemplate continuation inlining at each Jump
If not inlined, track join of parameters (or even of environs?)

Alternative to refining environments is to have projections (adjoint?)
   match p with (v1, v2) ->
   E

v1 = p.1, v2 = p.2 |- E ...

This seems fairly straightforward?
CSE: in LetVal, scan the environment. Could also do this in Match?
Projections only occur on neutral terms. Use this info.


Ah, but this misses the case where a continuation is invoked with implicit knowledge.

    if c1 then
      if c2 then k () else ...
    else
      if c2 then k () else ...

here k is always invoked when c2 is true
so maybe scan the environment back to the cont's environment, picking up facts?
     


*)


(*

LetCont 

*)
