open AST

(* Helper function to create a JSON string *)
let json_of_string s = "\"" ^ String.escaped s ^ "\""

(* Helper function to create a JSON object *)
let json_of_object obj = "{" ^ String.concat ", " obj ^ "}"

(* Helper function to create a JSON array *)
let json_of_array arr = "[" ^ String.concat ", " arr ^ "]"

let string_of_loc l =
  json_of_object [
    "\"pos\": " ^ (string_of_int l.pos);
    "\"len\": " ^ (string_of_int l.len)
  ]

let string_of_pos p =
  match p with
  | Pos loc -> json_of_object ["\"POS\": " ^ (string_of_loc loc)]
  | Txt string -> json_of_object ["\"Txt\": " ^ (json_of_string string)]

let string_of_set_or_rln sor =
  json_of_string (match sor with | SET -> "SET" | RLN -> "RLN")

let string_of_op2 o =
  json_of_string (match o with
  | Union -> "Union"
  | Inter -> "Inter"
  | Diff -> "Diff"
  | Seq -> "Seq"
  | Cartesian -> "Cartesian"
  | Add -> "Add"
  | Tuple -> "Tuple")

let string_of_op1 o =
  json_of_string (match o with
  | Plus -> "Plus"
  | Star -> "Star"
  | Opt -> "Opt"
  | Comp -> "Comp"
  | Inv -> "Inv"
  | ToId -> "ToId")

let string_of_konst k =
  match k with
  | Empty sor -> json_of_object ["\"Empty\": " ^ (string_of_set_or_rln sor)]
  | Universe sor -> json_of_object ["\"Universe\": " ^ (string_of_set_or_rln sor)]

let string_of_scope s =
  json_of_string (
  match s with 
    | Device -> "Device"
    | Kernel -> "Kernel"
    | Work_Group -> "Work_Group"
    | Sub_Group -> "Sub_Group"
    | Work_Item -> "Work_Item")

    let string_of_loc l =
      json_of_object [
        "\"pos\": " ^ (string_of_int l.pos);
        "\"len\": " ^ (string_of_int l.len)
      ]

let string_of_position p =  
  json_of_object [
  "\"pos_fname\": " ^ p.Lexing.pos_fname;
  "\"pos_lnum\": " ^ (string_of_int p.Lexing.pos_lnum); 
  "\"pos_bol \": " ^ (string_of_int p.Lexing.pos_bol); 
  "\"pos_cnum \": " ^ (string_of_int p.Lexing.pos_cnum)
  ]
let string_of_txtLoc_t t = json_of_object [
  "\"loc_start\": " ^ (string_of_position t.TxtLoc.loc_start);
  "\"loc_end\": " ^ (string_of_position t.TxtLoc.loc_end);
  "\"loc_ghost\": " ^ string_of_bool t.TxtLoc.loc_ghost]

let string_of_varset v = json_of_string (String.concat ", " (StringSet.elements v))


let rec string_of_exp e =
  match e with
  | Konst (t, konst) -> json_of_object ["\"Konst\": " 
   ^ json_of_array [(string_of_txtLoc_t t); (string_of_konst konst)]]
  | Tag (t, tag) -> json_of_object ["\"Tag\": " 
  ^ json_of_array [(string_of_txtLoc_t t); json_of_string tag]]
  | Var (t, var) -> json_of_object ["\"Var\": " 
  ^ json_of_array [(string_of_txtLoc_t t); json_of_string var]]
  | Op1 (t, op1, exp) -> json_of_object ["\"Op1\": " 
  ^ json_of_array [(string_of_txtLoc_t t); (string_of_op1 op1); (string_of_exp exp)]]
  | Op (t, op2, exp_list) -> json_of_object ["\"Op\": " 
  ^ json_of_array [(string_of_txtLoc_t t); (string_of_op2 op2); String.concat ", " ((List.map string_of_exp) exp_list)]]
  | App (t, exp1, exp2) -> json_of_object ["\"App\": " 
  ^ json_of_array [(string_of_txtLoc_t t); (string_of_exp exp1); (string_of_exp exp2)]]
  | Bind (t, binding_list, exp) -> json_of_object ["\"Bind\": " 
  ^ json_of_array [(string_of_txtLoc_t t); (string_of_binding_list binding_list); (string_of_exp exp)]]
  | BindRec (t, binding_list, exp) -> json_of_object ["\"BindRec\": " 
  ^ json_of_array [(string_of_txtLoc_t t); (string_of_binding_list binding_list); (string_of_exp exp)]]
  | Fun (t, pat, exp, var, varset) -> json_of_object ["\"Fun\": " 
  ^ json_of_array [(string_of_txtLoc_t t); (string_of_pat pat); (string_of_exp exp); json_of_string var; (string_of_varset varset)]]
  | ExplicitSet (t, exp_list) -> json_of_object ["\"ExplicitSet\": " 
  ^ json_of_array [(string_of_txtLoc_t t); (String.concat ", " ((List.map string_of_exp) exp_list))]]
  | Match (t, exp, clause_list, exp_option) -> json_of_object ["\"Match\": " 
  ^ json_of_array [(string_of_txtLoc_t t); (string_of_exp exp);
   (String.concat ", " ((List.map string_of_clause) clause_list)); (String.concat ", " ((List.map string_of_exp) (Option.to_list exp_option)))]]
  | MatchSet (t, exp1, exp2, set_clause) -> json_of_object ["\"MatchSet\": " 
  ^ json_of_array [(string_of_txtLoc_t t); (string_of_exp exp1); (string_of_exp exp2); (string_of_set_clause set_clause)]]
  | Try (t, exp1, exp2) -> json_of_object ["\"Try\": " 
  ^ json_of_array [(string_of_txtLoc_t t); (string_of_exp exp1); (string_of_exp exp2)]]
  | If (t, cond, exp1, exp2) -> json_of_object [
      "\"If\": " ^ json_of_array [(string_of_cond cond); (string_of_txtLoc_t t); (string_of_exp exp1); (string_of_exp exp2)]
    ]

  and string_of_set_clause sc =
  match sc with
   | EltRem (pat01, pat02, exp) -> json_of_object ["\"EltRem\": " 
   ^ json_of_array [(string_of_pat0 pat01); (string_of_pat0 pat02); (string_of_exp exp)]]
   | PreEltPost (pat01, pat02, pat03, exp) -> json_of_object ["\"PreEltPost\": " 
   ^ json_of_array [(string_of_pat0 pat01); (string_of_pat0 pat02); (string_of_pat0 pat03); (string_of_exp exp)]]

  and string_of_pat p = 
  match p with
    | Pvar pat0 -> json_of_object ["\"Pvar\": " 
    ^ json_of_string (string_of_pat0 pat0)]
    | Ptuple pat0_list -> json_of_object ["\"Ptuple\": " 
    ^ json_of_string (String.concat ", " ((List.map string_of_pat0) pat0_list))]

  and string_of_pat0 p = (String.concat ", " (Option.to_list p))

  and string_of_variant_cond vc =
  match vc with
    | Variant string -> json_of_object ["\"Variant\": " 
    ^ json_of_array [json_of_string string]]
    | OpNot variant_cond -> json_of_object ["\"OpNot\": " 
    ^ json_of_array [(string_of_variant_cond variant_cond)]]
    | OpAnd (variant_cond1, variant_cond2) -> json_of_object ["\"OpAnd\": " 
    ^ json_of_array [(string_of_variant_cond variant_cond1); (string_of_variant_cond variant_cond2)]]
    | OpOr (variant_cond1, variant_cond2) -> json_of_object ["\"OpOr\": " 
    ^ json_of_array [(string_of_variant_cond variant_cond1); (string_of_variant_cond variant_cond2)]]
    
  and string_of_cond c =
  match c with 
    | Eq (exp1, exp2) -> json_of_object ["\"Eq\": " 
    ^ json_of_array [(string_of_exp exp1); (string_of_exp exp2)]]
    | Subset (exp1, exp2) -> json_of_object ["\"Subset\": " 
    ^ json_of_array [(string_of_exp exp1); (string_of_exp exp2)]]
    | In (exp1, exp2) -> json_of_object ["\"In\": " 
    ^ json_of_array [(string_of_exp exp1); (string_of_exp exp2)]]
    | VariantCond variant_cond -> json_of_object ["\"VariantCond\": " 
    ^ json_of_array [(string_of_variant_cond variant_cond)]]

  and string_of_clause (string, exp) = json_of_array [json_of_string string; (string_of_exp exp)]

  and string_of_binding (t, pat, exp) =
    json_of_array [string_of_txtLoc_t t; string_of_pat pat; (string_of_exp exp)]

  and string_of_binding_list binding_list =
     (String.concat ", " ((List.map string_of_binding) binding_list))

let print_exp exp = Printf.printf "%s" (string_of_exp exp)

let string_of_do_test dt = 
  json_of_string (
  match dt with
    | Acyclic -> "Acyclic"
    | Irreflexive -> "Irreflexive"
    | TestEmpty -> "TestEmpty"
    )

let string_of_test t = 
  match t with
  | Yes do_test -> json_of_object ["\"Yes\": " ^ (string_of_do_test do_test)]
  | No do_test -> json_of_object ["\"No\": " ^ (string_of_do_test do_test)]

let string_of_test_type tt = 
  json_of_string (
  match tt with
  | Flagged -> "Flagged"
  | UndefinedUnless -> "UndefinedUnless"
  | Check -> "Check"
  | Assert -> "Assert"
  )
  
let string_of_app_test (t, pos, test, exp, string_op) = 
  json_of_array [string_of_txtLoc_t t; string_of_pos pos; string_of_test test; string_of_exp exp;
    json_of_string (String.concat " " (Option.to_list string_op))]

let string_of_is_rec r = 
  json_of_string (
  match r with 
  | IsRec -> "IsRec"
  | IsNotRec -> "IsNotRec"
  )

let rec string_of_ins i =
  match i with
    | Let (t, binding_list) -> json_of_object ["\"Let\": " 
    ^ json_of_array [string_of_txtLoc_t t; string_of_binding_list binding_list]]
    | Rec (t, binding_list, app_test_option) -> json_of_object ["\"Rec\": " 
    ^ json_of_array [string_of_txtLoc_t t; (string_of_binding_list binding_list); 
      String.concat ", " ((List.map string_of_app_test) (Option.to_list app_test_option))]]
    | InsMatch (t, exp, insclause_list, ins_list_option) -> json_of_object ["\"InsMatch\": " 
    ^ json_of_array [string_of_txtLoc_t t; 
      string_of_exp exp ^ String.concat ", " ((List.map string_of_insclause) insclause_list);
      String.concat ", " ((List.map string_of_ins_list) (Option.to_list ins_list_option))]]
    | Test (app_test, test_type) -> json_of_object ["\"Test\": " 
    ^ json_of_array [string_of_app_test app_test; string_of_test_type test_type]]
    | UnShow (t, string_list) -> json_of_object ["\"UnShow\": " 
    ^ json_of_array [string_of_txtLoc_t t; String.concat ", " string_list]]
    | Show (t, string_list) ->json_of_object ["\"Show\": " 
    ^ json_of_array [string_of_txtLoc_t t; String.concat ", " string_list]]
    | ShowAs (t, exp, string) -> json_of_object ["\"ShowAs\": " 
    ^ json_of_array [string_of_txtLoc_t t; string_of_exp exp; json_of_string string]]
    | Include (t, string) -> json_of_object ["\"Include\": " 
    ^ json_of_array [string_of_txtLoc_t t;json_of_string string]]
    | Procedure (t, var, pat, ins_list, is_rec) -> json_of_object ["\"Procedure\": " 
    ^ json_of_array [string_of_txtLoc_t t; json_of_string var; string_of_pat pat; string_of_ins_list ins_list; string_of_is_rec is_rec]]
    | Call (t, var, exp, string_option) -> json_of_object ["\"Call\": " 
    ^ json_of_array [string_of_txtLoc_t t; json_of_string var; string_of_exp exp; String.concat ", " (Option.to_list string_option)]]
    | Enum (t, var, tag_list) -> json_of_object ["\"Enum\": " 
    ^ json_of_array [string_of_txtLoc_t t; json_of_string var; String.concat ", " tag_list]]
    | Forall (t, var, exp, ins_list) -> json_of_object ["\"Forall\": " 
    ^ json_of_array [string_of_txtLoc_t t; json_of_string var; string_of_exp exp; string_of_ins_list ins_list]]
    | Debug (t, exp) -> json_of_object ["\"Debug\": " 
    ^ json_of_array [string_of_txtLoc_t t; string_of_exp exp]]
    | WithFrom (t, var, exp) -> json_of_object ["\"WithFrom\": " 
    ^ json_of_array [string_of_txtLoc_t t; json_of_string var; string_of_exp exp]]
    | Events (t, var, exp_list, bool) -> json_of_object ["\"Events\": " 
    ^ json_of_array [string_of_txtLoc_t t; json_of_string var; String.concat ", " ((List.map string_of_exp) exp_list); string_of_bool bool]]
    | IfVariant (t, variant_cond, ins_list1, ins_list2) -> json_of_object ["\"IfVariant\": " 
    ^ json_of_array [string_of_txtLoc_t t; string_of_variant_cond variant_cond; string_of_ins_list ins_list1; string_of_ins_list ins_list2]]

    and string_of_ins_list il = String.concat ", " ((List.map string_of_ins) il)

    and string_of_insclause (string, ins_list) = json_of_array [json_of_string string; string_of_ins_list ins_list]

let string_of_t (t, string, ins_list) = json_of_object ["\"Memory model\": " ^
  json_of_array [json_of_string (ModelOption.pp t); json_of_string string; string_of_ins_list ins_list]]

let print_t t = Printf.printf "%s" (string_of_t t) 
