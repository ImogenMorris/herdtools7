module Make (C:Sem.Config)(V:Value.S)
=
  struct
    module AArch64 = AArch64Arch.Make(C.PC)(V)
    module Act = MachAction.Make(AArch64)
    include SemExtra.Make(C)(AArch64)(Act)

(* Barrier pretty print *)
    let barriers = 
      let bs = AArch64Base.do_fold_dmb_dsb (fun h t -> h::t) []
      in List.map 
	   (fun b ->
	    { barrier = b;
	      pp = String.lowercase (AArch64Base.pp_barrier b)})
	   bs
    let isync = Some { barrier = AArch64Base.ISB;pp = "isb";}
 
(* Semantics proper *)
    let (>>=) = M.(>>=)
    let (>>*=) = M.(>>*=)
    let (>>|) = M.(>>|)
    let (>>!) = M.(>>!)
    let (>>::) = M.(>>::)

    let mk_read an loc v = Act.Access (Dir.R, loc, v,an)
					      
    let read_loc = 
      M.read_loc (mk_read AArch64.N)
    let read_reg r ii = 
      M.read_loc (mk_read AArch64.N) (A.Location_reg (ii.A.proc,r)) ii
    let read_mem a ii  = 
      M.read_loc (mk_read AArch64.N) (A.Location_global a) ii
    let read_mem_acquire a ii  = 
      M.read_loc (mk_read AArch64.A) (A.Location_global a) ii
    let read_mem_atomic a ii = 
      M.read_loc (mk_read AArch64.X) (A.Location_global a) ii
    let read_mem_atomic_acquire a ii = 
      M.read_loc (mk_read AArch64.XA) (A.Location_global a) ii
		 
    let write_loc loc v ii = 
      M.mk_singleton_es (Act.Access (Dir.W, loc, v, AArch64.N)) ii
    let write_reg r v ii = 
      M.mk_singleton_es (Act.Access (Dir.W, (A.Location_reg (ii.A.proc,r)), v,AArch64.N)) ii
    let write_mem a v ii  = 
      M.mk_singleton_es (Act.Access (Dir.W, A.Location_global a, v,AArch64.N)) ii
    let write_mem_release a v ii  = 
      M.mk_singleton_es (Act.Access (Dir.W, A.Location_global a, v,AArch64.L)) ii

    let write_mem_atomic a v resa ii =
      let eq = [M.VC.Assign (a,M.VC.Atom resa)] in
      M.mk_singleton_es_eq (Act.Access (Dir.W, A.Location_global a, v,AArch64.X)) eq ii
			   
    let write_mem_atomic_release a v resa ii =
      let eq = [M.VC.Assign (a,M.VC.Atom resa)] in
      M.mk_singleton_es_eq (Act.Access (Dir.W, A.Location_global a, v,AArch64.XL)) eq ii
			
    let create_barrier b ii = 
      M.mk_singleton_es (Act.Barrier b) ii

    let commit ii = 
      M.mk_singleton_es (Act.Commit) ii
		  
    let flip_flag v = M.op Op.Xor v V.one	
    let is_zero v = M.op Op.Eq v V.zero
    let is_not_zero v = M.op Op.Ne v V.zero
    
    let build_semantics ii = 
      M.addT (A.next_po_index ii.A.program_order_index)
        AArch64Base.( 
	match ii.A.inst with

	(* Branches *)
	| I_B l -> 
	   B.branchT l

	| I_BC(c,l)-> 
	   let cond = match c with
	     | NE -> is_not_zero
	     | EQ -> is_zero
	   in
	   (read_reg NZP ii) 
	   >>= cond
	   >>= fun v -> commit ii
	   >>= fun () -> B.bccT v l

	| I_CBZ(_,r,l) -> 
	   (read_reg r ii)
	   >>= is_zero
	   >>= fun v -> commit ii
	   >>= fun () -> B.bccT v l

	| I_CBNZ(_,r,l) -> 
	   (read_reg r ii)
	   >>= is_not_zero
	   >>= fun v -> commit ii
	   >>= fun () -> B.bccT v l

	(* Load and Store *)
	| I_LDR(_,rd,rs,kr) ->
	   begin match kr with
	   | K k ->
	      (read_reg rs ii)
	      >>= (fun v -> M.add v (V.asIntV k))
	   | RV(_,r) ->
	      (read_reg rs ii >>| read_reg r ii)
	      >>= (fun (v1,v2) -> M.add v1 v2)
	   end
	   >>= (fun a -> read_mem a ii)
	   >>= (fun v -> write_reg rd v ii)
	   >>! B.Next

	| I_LDAR(_,t,rd,rs) ->
	   (read_reg rs ii)
	   >>= fun a -> begin match t with
		 | XX ->
		    (write_reg ResAddr a ii >>|
		       (read_mem_atomic a ii
			>>= (fun v -> (write_reg rd v ii))))
		    >>! B.Next
		 | AA -> 
		    (read_mem_acquire a ii)
		    >>= (fun v -> (write_reg rd v ii))
		    >>! B.Next
		 | AX ->
		    (write_reg ResAddr a ii
		    >>| (read_mem_atomic_acquire a ii 
			 >>= (fun v -> write_reg rd v ii)))
		    >>! B.Next
	   end
	
	| I_STR(_,rs,rd,kr) ->
	   (read_reg rs ii >>|
	      match kr with
	      | K k ->
		 (read_reg rd ii)
		 >>= (fun v -> M.add v (V.asIntV k))
	      | RV(_,r) ->
		 (read_reg rd ii >>| read_reg r ii)
		 >>= (fun (v1,v2) -> M.add v1 v2))
	   >>= (fun (v,a) -> write_mem a v ii)
	   >>! B.Next

	| I_STLR(_,rs,rd) -> 
	   (read_reg rd ii >>| read_reg rs ii)
	   >>= (fun (a,v) -> write_mem_release a v ii)
	   >>! B.Next
	
	| I_STXR(_,t,rr,rs,rd) -> 
	   (read_reg rd ii >>| read_reg rs ii >>| read_reg ResAddr ii)
	   >>= (fun ((a,v),res) -> 
		(write_reg ResAddr V.zero ii
		 >>| M.altT
	               (write_reg rr V.one ii)
	               ((write_reg rr V.zero ii
			>>| match t with
			    | YY -> write_mem_atomic a v res ii
			    | LY -> write_mem_atomic_release a v res ii)
		       >>! ())))
	   >>! B.Next

	(* Operations *)
	| I_MOV(_,r,k) ->
	   write_reg r (V.asIntV k) ii >>! B.Next

	| I_SXTW(rd,rs) -> 
	   (read_reg rs ii)
	   >>= fun v -> (write_reg rd v ii)
	   >>! B.Next
	
	| I_OP3(_,op,rd,rn,kr) -> 
	   (read_reg rn ii >>|
	      match kr with
	      | K k -> M.add V.zero (V.asIntV k)
	      | RV(_,r) -> read_reg r ii
	   ) >>=
	     begin match op with
		   | ADD -> fun (v1,v2) -> M.add v1 v2
		   | EOR -> fun (v1,v2) -> M.op Op.Xor v1 v2
		   | SUBS -> fun (v1,v2) -> M.op Op.Sub v1 v2
	     end
	   >>= (fun v -> (write_reg rd v ii) 
			 >>| (write_reg NZP v ii))
	   >>! B.Next
		 
	(* Barrier *)
	| I_FENCE b -> 
	   (create_barrier b ii) >>! B.Next
      )
  end

