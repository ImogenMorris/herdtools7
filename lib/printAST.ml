open AST

let string_of_loc l = "{pos "^ (string_of_int l.pos) ^  "; len " ^ (string_of_int l.len) ^ ";}"

let string_of_pos p = 
  match p with
  | Pos loc -> "(POS " ^ (string_of_loc loc) ^ ")"
  | Txt string -> "(Txt " ^ string ^ ")"

let string_of_set_or_rln sor =
  match sor with
  | SET -> "SET"
  | RLN -> "RLN"

let string_of_op2 o =
  match o with
  | Union -> "Union"
  | Inter -> "Inter"
  | Diff -> "Diff"
  | Seq -> "Seq"
  | Cartesian -> "Cartesian"
  | Add -> "Add"
  | Tuple -> "Tuple"

let string_of_op1 o =
  match o with
    | Plus -> "Plus"
    | Star -> "Star"
    | Opt -> "Opt"
    | Comp -> "Comp"
    | Inv -> "Inv"
    | ToId -> "ToId"
  
let string_of_konst k =
  match k with
    | Empty sor -> "(Empty " ^ (string_of_set_or_rln sor) ^ ")"
    | Universe sor -> "(Universe " ^ (string_of_set_or_rln sor) ^ ")"

(*  type var = string
  type tag = string*)


(*  type varset = StringSet.t*) (*t is just a string so does it matter?*)

let string_of_scope s =
  match s with 
    | Device -> "Device"
    | Kernel -> "Kernel"
    | Work_Group -> "Work_Group"
    | Sub_Group -> "Sub_Group"
    | Work_Item -> "Work_Item"

let string_of_position p =
  "{pos_fname " ^ p.Lexing.pos_fname ^ "; pos_lnum " ^ (string_of_int p.Lexing.pos_lnum) ^
   "; pos_bol " ^ (string_of_int p.Lexing.pos_bol) ^ "; pos_cnum " ^ (string_of_int p.Lexing.pos_cnum) ^ ";}"

let string_of_txtLoc_t t =
  "{loc_start " ^ (string_of_position t.TxtLoc.loc_start) ^ "; loc_end " ^ (string_of_position t.TxtLoc.loc_end) ^
   "; loc_ghost" ^ string_of_bool t.TxtLoc.loc_ghost ^ ";}"

(*   type position = {
    pos_fname : string;
    pos_lnum : int;
    pos_bol : int;
    pos_cnum : int;
  }

    type t = {
      loc_start : Lexing.position ;
      loc_end : Lexing.position ;
      loc_ghost : bool ;
      }*)

let string_of_varset v = String.concat " " (StringSet.elements v)
  
let rec string_of_exp e =
  match e with
  | Konst (t, konst) -> "Konst (" ^ (string_of_txtLoc_t t) ^ (string_of_konst konst) ^ ")"
  | Tag (t, tag) -> "Tag (" ^ (string_of_txtLoc_t t) ^ tag ^ ")"
  | Var (t, var) -> "Var (" ^ (string_of_txtLoc_t t) ^ var ^ ")"
  | Op1 (t, op1, exp) -> "Op1 (" ^ string_of_txtLoc_t t ^ (string_of_op1 op1) ^ (string_of_exp exp) ^ ")"
  | Op (t, op2, exp_list) -> "Op (" ^ string_of_txtLoc_t t ^ 
                 (string_of_op2 op2) ^ String.concat " " ((List.map string_of_exp) exp_list) ^ ")"
  | App (t, exp1, exp2) -> "App (" ^ string_of_txtLoc_t t ^ 
                 (string_of_exp exp1) ^ (string_of_exp exp2) ^ ")"
  | Bind (t, binding_list, exp) -> "Bind (" ^ string_of_txtLoc_t t ^ 
  string_of_binding_list binding_list ^ (string_of_exp exp) ^ ")" (*string_of_binding defined below*)
  | BindRec (t, binding_list, exp) -> "BindRec (" ^ string_of_txtLoc_t t ^ 
  string_of_binding_list binding_list ^ (string_of_exp exp) ^ ")" 
  | Fun (t, pat, exp, var, varset) -> "Fun (" ^ string_of_txtLoc_t t ^ 
  string_of_pat pat ^ (string_of_exp exp) ^ var ^ (string_of_varset varset) ^ ")" 
  | ExplicitSet (t, exp_list) -> "ExplicitSet (" ^ string_of_txtLoc_t t ^ 
   String.concat " " ((List.map string_of_exp) exp_list) ^ ")"
  | Match (t, exp, clause_list, exp_option) -> "Match (" ^ string_of_txtLoc_t t ^ (string_of_exp exp) ^ 
  String.concat " " ((List.map string_of_clause) clause_list) ^ string_of_exp (Option.get exp_option) ^ ")"
  | MatchSet (t, exp1, exp2, set_clause) -> "MatchSet (" ^ string_of_txtLoc_t t ^ (string_of_exp exp1) ^ 
  (string_of_exp exp2) ^
  (string_of_set_clause set_clause) ^ ")"
  | Try (t, exp1, exp2) -> "Try (" ^ string_of_txtLoc_t t ^ (string_of_exp exp1) ^ (string_of_exp exp2) ^ ")"
  | If (t, cond, exp1, exp2) -> "If (" ^ string_of_cond cond
   ^ string_of_txtLoc_t t ^ (string_of_exp exp1) ^ (string_of_exp exp2) ^ ")"

  and string_of_set_clause sc =
  match sc with
   | EltRem (pat01, pat02, exp) -> "EltRem (" ^ string_of_pat0 pat01 
   ^ string_of_pat0 pat02 ^ (string_of_exp exp) ^ ")"
   | PreEltPost (pat01, pat02, pat03, exp) -> "PreEltPost (" ^ string_of_pat0 pat01 
   ^ string_of_pat0 pat02 ^ string_of_pat0 pat03 ^ (string_of_exp exp) ^ ")"

  and string_of_pat p = 
  match p with
    | Pvar pat0 -> "Pvar (" ^ string_of_pat0 pat0 ^ ")"
    | Ptuple pat0_list -> "Ptuple (" ^ String.concat " " ((List.map string_of_pat0) pat0_list) ^ ")"

  and string_of_pat0 p = Option.get p

  and string_of_variant_cond vc =
  match vc with
    | Variant string -> "Variant (" ^ string ^ ")"
    | OpNot variant_cond -> "OpNot (" ^ string_of_variant_cond variant_cond ^ ")"
    | OpAnd (variant_cond1, variant_cond2) -> "OpAnd (" ^ string_of_variant_cond variant_cond1 ^ string_of_variant_cond variant_cond2 ^ ")"
    | OpOr (variant_cond1, variant_cond2) -> "OpOr (" ^ string_of_variant_cond variant_cond1 ^ string_of_variant_cond variant_cond2 ^ ")"
    
  and string_of_cond c =
  match c with 
    | Eq (exp1, exp2) -> "Eq (" ^ (string_of_exp exp1) ^ (string_of_exp exp2) ^ ")"
    | Subset (exp1, exp2) -> "Subset (" ^ (string_of_exp exp1) ^ (string_of_exp exp2) ^ ")"
    | In (exp1, exp2) ->  "In (" ^ (string_of_exp exp1) ^ (string_of_exp exp2) ^ ")"
    | VariantCond variant_cond -> "VariantCond (" ^ string_of_variant_cond variant_cond ^ ")"

  and string_of_clause (string, exp) = string ^ (string_of_exp exp)

  and string_of_binding (t, pat, exp) = string_of_txtLoc_t t ^ string_of_pat pat ^ string_of_exp exp

  and string_of_binding_list binding_list = String.concat " " ((List.map string_of_binding) binding_list)

let print_exp exp = Printf.printf "%s" (string_of_exp exp)

let string_of_do_test dt = 
  match dt with
    | Acyclic -> "Acyclic"
    | Irreflexive -> "Irreflexive"
    | TestEmpty -> "TestEmpty"

let string_of_test t = 
  match t with
  | Yes do_test -> "Yes (" ^ (string_of_do_test do_test) ^ ")"
  | No do_test -> "No (" ^ (string_of_do_test do_test) ^ ")"

let string_of_test_type tt = 
  match tt with
  | Flagged -> "Flagged"
  | UndefinedUnless -> "UndefinedUnless"
  | Check -> "Check"
  | Assert -> "Assert"
  
let string_of_app_test (t, pos, test, exp, string_op) = 
    string_of_txtLoc_t t ^ string_of_pos pos ^ string_of_test test ^ string_of_exp exp 
    ^ Option.get string_op

let string_of_is_rec r = 
  match r with 
  | IsRec -> "IsRec"
  | IsNotRec -> "IsNotRec"

let string_of_ins i =
  match i with
    | Let (t, binding_list) -> "Let (" ^ string_of_txtLoc_t t ^ string_of_binding_list binding_list ^ ")"
    | Rec (t, binding_list, app_test_option) -> "Rec (" ^ string_of_txtLoc_t t ^ 
    (string_of_binding_list binding_list) ^ (Option.get app_test_option |> string_of_app_test) ^ ")"
    | InsMatch (t, exp, insclause_list, ins_list_option)  -> "InsMatch (" ^ string_of_txtLoc_t t
     ^ string_of_exp exp ^ String.concat " " ((List.map string_of_insclause) insclause_list) 
     ^ (Option.get ins_list_option |> string_of_ins_list) ")"
    | Test (app_test, test_type) -> "Test (" ^ string_of_app_test app_test ^ string_of_test_type test_type ")"
    | UnShow (t, string_list) -> "UnShow (" ^ string_of_txtLoc_t t ^  ^ ")"
    | Show (t, string_list) -> "Show (" ^ string_of_txtLoc_t t ^  ^ ")"
    | ShowAs (t, exp, string) -> "ShowAs (" ^ string_of_txtLoc_t t ^  ^ ")"
    | Include (t, string) -> "Include (" ^ string_of_txtLoc_t t ^  ^ ")"
    | Procedure (t, var, pat, ins list, is_rec) -> "Procedure (" ^ string_of_txtLoc_t t ^  ^ ")"
    | Call (t, var, exp, string option) -> " (" ^ string_of_txtLoc_t t ^  ^ ")"
    | Enum (t, var, tag list) -> " (" ^ string_of_txtLoc_t t ^  ^ ")"
    | Forall (t, var, exp, ins list) -> " (" ^ string_of_txtLoc_t t ^  ^ ")"
    | Debug (t, exp) -> " (" ^ string_of_txtLoc_t t ^  ^ ")"
    | WithFrom (t, var, exp) -> " (" ^ string_of_txtLoc_t t ^  ^ ")"
    | Events (t, var, exp list, bool) -> " (" ^ string_of_txtLoc_t t ^  ^ ")"
    | IfVariant (t, variant_cond, ins list, ins list) -> " (" ^ string_of_txtLoc_t t ^  ^ ")"
  (*
  type ins =
    | Let of TxtLoc.t * binding list
    | Rec of  TxtLoc.t * binding list * app_test option
    | InsMatch of TxtLoc.t * exp * insclause list * ins list option
    | Test of  app_test * test_type
    | UnShow of  TxtLoc.t * string list
    | Show of  TxtLoc.t * string list
    | ShowAs of  TxtLoc.t * exp * string
    | Include of  TxtLoc.t * string (* file name, interpreter will read/parse file... *)
    | Procedure of  TxtLoc.t * var * pat * ins list * is_rec
    | Call of  TxtLoc.t * var * exp * string option (* optional name, for skip *)
    | Enum of TxtLoc.t * var * tag list
    | Forall of  TxtLoc.t * var * exp * ins list
    | Debug of TxtLoc.t * exp
    | WithFrom of TxtLoc.t * var * exp (* set of relations *)
  (*For bell files*)
    | Events of TxtLoc.t * var * exp list * bool (* define default *)
  (*Conditional, on variant as a string, avoiding dependency on herd/variant.ml *)
    | IfVariant of TxtLoc.t * variant_cond * ins list * ins list
  
  and insclause = string * ins list
  
  
  
  (** Name X model definition *)
  type t = ModelOption.t * string * ins list*)