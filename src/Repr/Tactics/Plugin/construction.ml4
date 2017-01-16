DECLARE PLUGIN "construction_plugin"

open Inductiveops
open Pp

(* Write a tactic that inspecs a type introduces all primative constructions
   (i.e., constants) of that type into the hypothesis *)

(* Making progress. In particular, we need to inspec:
    - declarations.ml for inspecting all possible constructions of a type
    - pre_env.ml for getting information from declarations.ml
    - names.ml for querying the enviornment and declarations *)


(* Ignore universe information for now *)

let constrs_from_type env types =
  let pind = Inductive.find_inductive env types in
  let fam = Inductiveops.make_ind_family pind in
  let constrs = Inductiveops.get_constructors env fam in
  constrs

let intro_nary_constrs constrs =
  (* msg_info (Pp.str (Printf.sprintf "Length of constrs %d" (Array.length constrs))) ; *)
  Array.fold_left (
    fun m cs -> 
      (* msg_info (Pp.str (Printf.sprintf "cs_params:%d cs_nargs:%d" (List.length cs.cs_params) cs.cs_nargs)) ; *)
      if cs.cs_nargs == 0
        then begin
          let c = Inductiveops.build_dependent_constructor cs in
          Proofview.tclTHEN (Tactics.letin_tac None Names.Anonymous c None Locusops.nowhere) m
        end
      else m
  ) (Proofview.tclUNIT ()) constrs 
  
module ConstructionTactics = struct
  
  let gen_constructors types =
    Proofview.Goal.enter ( 
      fun gl ->
        let constrs = constrs_from_type (Proofview.Goal.env gl) types in
        intro_nary_constrs constrs 
    )

end 

TACTIC EXTEND gen_constructors
| ["gen_constructors" constr(c)] -> [ConstructionTactics.gen_constructors c]
END
