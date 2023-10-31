open AST

let string_of_loc l = "{pos "^ (string_of_int l.pos) ^  "; len " ^ (string_of_int l.len) ^ ";}"

let string_of_pos p = 
  match p with
  | Pos loc -> "(POS " ^ (loc loc) ^ ")"
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


  type varset = StringSet.t

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
  "{loc_start " ^ (string_of_position t.txtLoc.loc_start) ^ "; loc_end " ^ (string_of_position t.txtLoc.loc_end) ^
   "; loc_ghost" ^ string_of_bool t.txtLoc.loc_ghost ^ ";}"

   

   type position = {
    pos_fname : string;
    pos_lnum : int;
    pos_bol : int;
    pos_cnum : int;
  }

    type t = {
      loc_start : Lexing.position ;
      loc_end : Lexing.position ;
      loc_ghost : bool ;
      }
  
let exp e =
  match e with
  | Konst of TxtLoc.t * konst -> "(" ^ (konst konst) ^ ")"
  | Tag of TxtLoc.t * tag
  | Var of TxtLoc.t * var
  | Op1 of  TxtLoc.t * op1 * exp
  | Op of  TxtLoc.t * op2 * exp list
  | App of  TxtLoc.t * exp * exp
  | Bind  of  TxtLoc.t * binding list * exp
  | BindRec  of  TxtLoc.t * binding list * exp
  | Fun of  TxtLoc.t * pat * exp *
        var (* name *) * varset (* free vars *)
  | ExplicitSet of TxtLoc.t * exp list
  | Match of TxtLoc.t * exp * clause list * exp option
  | MatchSet of TxtLoc.t * exp * exp * set_clause
  | Try of TxtLoc.t * exp * exp
  | If of TxtLoc.t * cond * exp * exp

  
and set_clause =
  | EltRem of pat0 * pat0 * exp
  | PreEltPost of pat0 * pat0 * pat0 * exp
  
  
  and pat = Pvar of pat0 | Ptuple of pat0 list
  
  and pat0 = var option
  
  and variant_cond =
    | Variant of string
    | OpNot of variant_cond
    | OpAnd of variant_cond * variant_cond
    | OpOr of variant_cond * variant_cond
  
  and cond =
  | Eq of exp * exp | Subset of exp * exp | In of exp * exp
  | VariantCond of variant_cond
  
  and clause = string * exp
  
  and binding = TxtLoc.t * pat * exp
  
  
  type exp =
    | Konst of  TxtLoc.t * konst
    | Tag of TxtLoc.t * tag
    | Var of TxtLoc.t * var
    | Op1 of  TxtLoc.t * op1 * exp
    | Op of  TxtLoc.t * op2 * exp list
    | App of  TxtLoc.t * exp * exp
    | Bind  of  TxtLoc.t * binding list * exp
    | BindRec  of  TxtLoc.t * binding list * exp
    | Fun of  TxtLoc.t * pat * exp *
          var (* name *) * varset (* free vars *)
    | ExplicitSet of TxtLoc.t * exp list
    | Match of TxtLoc.t * exp * clause list * exp option
    | MatchSet of TxtLoc.t * exp * exp * set_clause
    | Try of TxtLoc.t * exp * exp
    | If of TxtLoc.t * cond * exp * exp
  
  and set_clause =
    | EltRem of pat0 * pat0 * exp
    | PreEltPost of pat0 * pat0 * pat0 * exp
  
  
  and pat = Pvar of pat0 | Ptuple of pat0 list
  
  and pat0 = var option
  
  and variant_cond =
    | Variant of string
    | OpNot of variant_cond
    | OpAnd of variant_cond * variant_cond
    | OpOr of variant_cond * variant_cond
  
  and cond =
  | Eq of exp * exp | Subset of exp * exp | In of exp * exp
  | VariantCond of variant_cond
  
  and clause = string * exp
  
  and binding = TxtLoc.t * pat * exp
  
  type do_test = Acyclic | Irreflexive | TestEmpty
  type test = Yes of do_test | No of do_test
  type test_type = Flagged | UndefinedUnless | Check | Assert
  type app_test = TxtLoc.t * pos * test * exp * string option
  type is_rec = IsRec | IsNotRec
  
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
  type t = ModelOption.t * string * ins list