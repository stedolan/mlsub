(* ocaml -noprompt -no-version < ../test/partition_refinement.ml *)
(*#use "partition_refinement.ml";;*)
let p = make 42;;
to_sets p;;
refine p [1;2;3;4;5;6];;
to_sets p;;









refine p [1;2;3];
refine p [3;7;9];
to_sets p;;
