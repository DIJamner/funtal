module Compiler = struct

  open Syntax
  open FTAL
  

  type atstackelem = ABinding of string * A.ty | TElem of TAL.t
  type atstack = ATStack of atstackelem list * TAL.sigma

  let toTalHVal = function
  | (TAL.Ref, TAL.PTuple l) -> TAL.TTupleRef l

  let rec compileType = function 
  | A.TyVar s -> TAL.TVar s
  | A.TyBool -> TAL.TInt 
  | A.TyExist (a,typ) -> TAL.TExists (a,compileType typ)
  | A.TyRec (a, typ) -> TAL.TRec (a,compileType typ)
  | A.TyRef htyp -> (toTalHVal (TAL.Ref, compileHType htyp)) (*TODO*)
  | A.TyBox htyp -> TAL.TBox (compileHType htyp)
  and compileHType = function
  | A.TyCode (aas, args, res) -> 
    let zeta = gen_sym ~pref:"z"() in
    let epsilon = gen_sym ~pref:"e"() in
    let raTy = TAL.TBox (PBlock ([], [("r1", compileType res)],
      SAbstract ([], zeta), QEpsilon epsilon)) in
    let delta = (TAL.DZeta zeta)::(TAL.DEpsilon epsilon)
      ::(List.map (fun x -> TAL.DAlpha x) aas) in
    PBlock (delta, [("ra", raTy)], 
      SAbstract (List.map compileType args, zeta), QR"ra")
  | A.TyTuple typs -> PTuple (List.map compileType typs)
  (* TODO | A.TySum (tyl, tyr) -> PSum (compileType tyl, compileType tyr) *)


  (* Compiles closed values *)
  let rec compileValue = function
  | A.TUnit l -> Some (TAL.WUnit l)
  | A.TBool (l, true) -> Some (TAL.WInt (l, 1))
  | A.TBool (l, false) -> Some (TAL.WInt (l, 0))
  | A.TInst (l, v, typ) -> begin match compileValue v with
    | Some w -> Some(TAL.WApp (l, w, [OT (compileType typ)]))
    | None -> None
    end
  | A.TPack (l, typ, v, a, etyp) -> 
    begin match compileValue v with
    | Some w -> Some (TAL.WPack (l, compileType typ, w, a, compileType etyp))
    | None -> None
    end
  | A.TFold (l, a, typ, v) -> begin match v with
    | Some w -> Some (TAL.WFold (l, a, compileType typ, w))
    | None -> None
    end
  | A.TLoc (l, loc) -> Some(TAL.WLoc (l, loc))


  let rec optionMap f = function
  | [] -> []
  | a::tl -> begin match f a with
    | Some b -> b :: (optionMap f tl)
    | None -> optionMap f tl
    end

  (* assumes that hv typechecks at type psi *)
  let rec compileHeapValue initialHeapTy = function
  | HCode (l, aas, xts, body) -> 
    (*TODO: handle fail case *)
    let TyCode (_, argTys, resTy) = A.getExpType aas xts body in
    let revArgTys = List.reverse argTys in
    let transArgTys = List.map compileType revArgTys in
    let zeta = gen_sym(pref="z") in
    let epsilon = gen_sym(pref="e") in
    let retLoc = gen_sym(pref="l") in
    let talResTy = compileType resTy in
    let raTy = TBox (PBlock ([], [("r1", talResTy)],
      SAbstract ([], zeta), QEpsilon epsilon)) in
    let argStack = ATStack (TElem raTy :: List.rev_map ABinding xts,
      SAbstract ([], zeta)) in
    let (bodyInstrs, bodyHeap, bodyHeapTy) =
      compileExpr initialHeapTy aas argStack body zeta epsilon (QI 0) in
    let h = TAL.HCode (DEpsilon epsilon :: DZeta zeta :: List.map DAlpha aas,
      [("ra", raTy)], SAbstract (transArgTys, zeta), QR"ra",
      Isalloc (l,1) ::
      Isst (l,0, "ra")::
      Imv (l, "ra", UW (WApp (l, WLoc (l, retloc), OQ (QI epsilon) :: 
                                OS (SAbstract([],zeta)) ::
                                List.map (OT . TVar) aas)))::
      bodyInstrs) in
    let retCode = TAL.HCode (DEpsilon epsilon :: DZeta zeta :: List.map DAlpha aas,
      ["r1", talResTy], SAbstract (raTy::transArgTys, zeta), QI 0,
      [Isld (l,"ra", 0),
      Isfree (l, List.len xts + 1),
      Iret (l, "ra", "r1")]) in
    let heap = (retLoc, retCode)::bodyHeap in
    let heapTy = (retLoc, PBlock (DEpsilon epsilon :: DZeta zeta :: List.map DAlpha aas,
      ["r1", talResTy], SAbstract (raTy::transArgTys, zeta), QI 0))::bodyHeapTy in  
    (h, heap, heapTy)
  | HTuple vals -> 
    let tvals = optionMap compileValue vals in
    (HTuple tvals, [], [])
  (* | HInl val -> ...
  | HInr val -> ... *)  

end