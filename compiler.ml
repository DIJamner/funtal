module Compiler = struct

  let rec compileType = function 
  | TyVar s -> TAL.TVar s
  | TyBool -> TAL.TInt 
  | TyExist (a,typ) -> TExist (a,compileType typ)
  | TyRec (a, typ) -> TRec (a,compileType typ)
  | TyRef htyp -> TRef (compileHType htyp)
  | TyBox htyp -> TBox (compileHType htyp)
  and compileHType = function
  | TyCode (aas, args, res) -> 
    let zeta = gen_sym(pref="z") in
    let epsilon = gen_sym(pref="e") in
    let raTy = TBox (PBlock ([], [("r1", compileType res)],
      SAbstract ([], zeta), QEpsilon epsilon)) in
    PBlock (zeta::epsilon::aas, [("ra", raTy)], 
      SAbstract (List.map compileType args, zeta), QR"ra")
  | TyTuple typs -> PTuple (List.map compileType typs)
  | TySum (tyl, tyr) -> PSum (compileType tyl, compileType tyr)


  (* Compiles closed values *)
  let rec compileValue = function
  | TUnit l -> Some (WUnit l)
  | TBool (l, true) -> Some (WInt (l, 1))
  | TBool (l, false) -> Some (WInt (l, 0))
  | TInst (l, v, typ) -> begin match compileValue v with
    | Some w -> WApp (l, w, [compileType typ])
    | None -> None
    end
  | TPack (l, typ, v, a, etyp) -> 
    begin match compileValue v with
    | Some w -> Some (WPack (l, compileType typ, w, a, compileType etyp))
    | None -> None
    end
  | TFold (l, a, typ, v) -> begin match v with
    | Some w -> Some (WFold (l, a, compileType typ, w))
    | None -> None
    end
  | TLoc (l, loc) -> WLoc (l, loc)


  let rec optionMap f = function
  | [] -> []
  | a::tl -> begin match f a with
    | Some b -> b :: (optionMap f tl)
    | None -> optionMap f tl
    end

  (* assumes that hv typechecks at type psi *)
  let rec compileHeapValue initialHeapTy = function
  | HCode (_, aas, xts, body) -> 
    (*TODO: handle fail case *)
    let TyCode (l, argTys, resTy) = A.getExpType aas xts body in
    let revArgTys = List.reverse argTys in
    let transArgTys = List.map compileType revArgTys in
    let zeta = gen_sym(pref="z") in
    let epsilon = gen_sym(pref="e") in
    let retLoc = gen_sym(pref="l") in
    let (bodyInstrs, bodyHeap, bodyHeapTy) =
      compileExpr initialHeapTy aas [...] body zeta epsilon (QI 0) in
    let raTy = TBox (PBlock ([], [("r1", compileType resTy)],
      SAbstract ([], zeta), QEpsilon epsilon)) in
    let h = TAL.HCode (DEpsilon epsilon :: DZeta zeta :: List.map DAlpha aas,
      [("ra", raTy)], SAbstract (transArgTys, zeta), QR"ra",
      Isalloc (l,1) ::
      Isst (l,0, "ra")::
      Imv (l, "ra", UW (WApp (l, WLoc (l, retloc), OQ (QI epsilon) :: 
                                OS (SAbstract([],zeta)) ::
                                List.map (OT . TVar) aas)))::
      bodyInstrs) in
    let heap = ... in
    let heapTy = ... in  
    (h, heap, heapTy)
  | HTuple vals -> 
    let tvals = optionMap compileValue vals in
    (HTuple tvals, [], [])
  (* | HInl val -> ...
  | HInr val -> ... *)  

end