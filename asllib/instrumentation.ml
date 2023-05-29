module Rule = struct
  type t =
    | Lit
    | IgnoreTypedExpr
    | ELocalVar
    | GlobalConst
    | Binop
    | Unop
    | ECond
    | ESlice
    | ECall
    | ERecord
    | GetRecordField
    | GetBitFields
    | GetBitField
    | EConcat
    | LEIgnore
    | LETyped
    | LELocalVar
    | LESlice
    | LESetRecordField
    | LESetBitField
    | LESetBitFields
    | LETupleUnpack
    | Pass
    | Assign
    | ReturnOne
    | ReturnNone
    | Then
    | SCall
    | SCond
    | Assert

  let to_string : t -> string = function
    | Lit -> "Lit"
    | IgnoreTypedExpr -> "IgnoreTypedExpr"
    | ELocalVar -> "ELocalVar"
    | GlobalConst -> "GlobalConst"
    | Binop -> "Binop"
    | Unop -> "Unop"
    | ECond -> "ECond"
    | ESlice -> "ESlice"
    | ECall -> "ECall"
    | ERecord -> "ERecord"
    | GetRecordField -> "GetRecordField"
    | GetBitFields -> "GetBitFields"
    | GetBitField -> "GetBitField"
    | EConcat -> "EConcat"
    | LEIgnore -> "LEIgnore"
    | LETyped -> "LETyped"
    | LELocalVar -> "LELocalVar"
    | LESlice -> "LESlice"
    | LESetRecordField -> "LESetRecordField"
    | LESetBitField -> "LESetBitField"
    | LESetBitFields -> "LESetBitFields"
    | LETupleUnpack -> "LETupleUnpack"
    | Pass -> "Pass"
    | Assign -> "Assign"
    | ReturnOne -> "ReturnOne"
    | ReturnNone -> "ReturnNone"
    | Then -> "Then"
    | SCall -> "SCall"
    | SCond -> "SCond"
    | Assert -> "Assert"

  let pp f r = to_string r |> Format.pp_print_string f

  let all =
    [
      Lit;
      IgnoreTypedExpr;
      ELocalVar;
      GlobalConst;
      Binop;
      Unop;
      ECond;
      ESlice;
      ECall;
      ERecord;
      GetRecordField;
      GetBitFields;
      GetBitField;
      EConcat;
      LEIgnore;
      LETyped;
      LELocalVar;
      LESlice;
      LESetRecordField;
      LESetBitField;
      LESetBitFields;
      LETupleUnpack;
      Pass;
      Assign;
      ReturnOne;
      ReturnNone;
      Then;
      SCall;
      SCond;
      Assert;
    ]

  let all_nb = List.length all

  let index =
    let tbl : (t, int) Hashtbl.t = Hashtbl.create all_nb in
    let () = List.iteri (fun i r -> Hashtbl.add tbl r i) all in
    let tbl = Hashtbl.rebuild tbl in
    Hashtbl.find tbl
end

type rule = Rule.t

module type INSTR = sig
  val use : rule -> unit
  val use_with : 'a -> rule -> 'a
end

module type BUFFER = sig
  val push : rule -> unit
  val reset : unit -> unit
  val get : unit -> rule list
end

module Make (Buffer : BUFFER) : INSTR = struct
  let use = Buffer.push

  let use_with (x : 'a) r : 'a =
    Buffer.push r;
    x
end

module NoBuffer : BUFFER = struct
  let push = Fun.const ()
  let reset () = ()
  let get () = []
end

module SingleBuffer : BUFFER = struct
  let _buffer : rule list ref = ref []
  let reset () = _buffer := []
  let get () = !_buffer
  let push r = _buffer := r :: !_buffer
end

module SingleSetBuffer : BUFFER = struct
  let _buffer : (rule, unit) Hashtbl.t = Hashtbl.create Rule.all_nb
  let reset () = Hashtbl.clear _buffer
  let get () = Hashtbl.to_seq_keys _buffer |> List.of_seq
  let push r = Hashtbl.replace _buffer r ()
end

module NoInstr = Make (NoBuffer)
module SingleInstr = Make (SingleBuffer)
module SingleSetInstr = Make (SingleSetBuffer)
