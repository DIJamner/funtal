open Syntax
open Typecheck.FTAL
open Typecheck.TAL
open TAL

type atstackelem = ABinding of string * A.ty | TElem of t
type atstack = ATStack of atstackelem list * sigma

let toTalHVal = function
| (Ref, PTuple l) -> TTupleRef l
(* TODO: other cases *)

let rec compileType = function 
| A.TyVar s -> TVar s
| A.TyUnit -> TUnit
| A.TyBool -> TInt 
| A.TyExist (a,typ) -> TExists (a,compileType typ)
| A.TyRec (a, typ) -> TRec (a,compileType typ)
| A.TyRef htyp -> (toTalHVal (Ref, compileHType htyp)) (*TODO*)
| A.TyBox htyp -> TBox (compileHType htyp)
and compileHType = function
| A.TyCode (aas, args, res) -> 
  let zeta = gen_sym ~pref:"z"() in
  let epsilon = gen_sym ~pref:"e"() in
  let raTy = TBox (PBlock ([], [("r1", compileType res)],
    SAbstract ([], zeta), QEpsilon epsilon)) in
  let delta = (DZeta zeta)::(DEpsilon epsilon)
    ::(List.map (fun x -> DAlpha x) aas) in
  PBlock (delta, [("ra", raTy)], 
    SAbstract (List.map compileType args, zeta), QR"ra")
| A.TyTuple typs -> PTuple (List.map compileType typs)
(* TODO | A.TySum (tyl, tyr) -> PSum (compileType tyl, compileType tyr) *)


(* Compiles closed values *)
let rec compileValue = function
| A.TUnit l -> Some (WUnit l)
| A.TBool (l, true) -> Some (WInt (l, 1))
| A.TBool (l, false) -> Some (WInt (l, 0))
| A.TInst (l, v, typ) -> begin match compileValue v with
  | Some w -> Some(WApp (l, w, [OT (compileType typ)]))
  | None -> None
  end
| A.TPack (l, typ, v, a, etyp) -> 
  begin match compileValue v with
  | Some w -> Some (WPack (l, compileType typ, w, a, compileType etyp))
  | None -> None
  end
| A.TFold (l, a, typ, v) -> begin match compileValue v with
  | Some w -> Some (WFold (l, a, compileType typ, w))
  | None -> None
  end
| A.TLoc (l, loc) -> Some(WLoc (l, loc))
| _ -> None


let rec optionMap f = function
| [] -> []
| a::tl -> begin match f a with
  | Some b -> b :: (optionMap f tl)
  | None -> optionMap f tl
  end

(* assumes that hv typechecks at type psi *)
let rec compileHeapValue initialHeapTy = function
| A.HCode (l, aas, xts, body) -> 
  (*TODO: handle fail case *)
  let resTy = Typecheck.A.tc_t initialHeapTy aas xts body in
  let revArgTys = List.rev_map snd xts in
  let transArgTys = List.map compileType revArgTys in
  let zeta = gen_sym ~pref:"z" () in
  let epsilon = gen_sym ~pref:"e" () in
  let retLoc = gen_sym ~pref:"l" () in
  let talResTy = compileType resTy in
  let raTy = TBox (PBlock ([], [("r1", talResTy)],
    SAbstract ([], zeta), QEpsilon epsilon)) in
  let argStack = ATStack (TElem raTy :: List.rev_map (fun (x,t) -> ABinding (x,t)) xts,
    SAbstract ([], zeta)) in
  let (bodyInstrs, bodyHeap, bodyHeapTy) =
    compileExpr initialHeapTy aas argStack body zeta epsilon (QI 0) in
  let h = HCode (DEpsilon epsilon :: DZeta zeta :: List.map (fun x -> DAlpha x) aas,
    [("ra", raTy)], SAbstract (transArgTys, zeta), QR"ra",
    Isalloc (l,1) ::
    Isst (l,0, "ra")::
    Imv (l, "ra", UW (l, WApp (l, WLoc (l, retLoc), OQ (QEpsilon epsilon) :: 
                              OS (SAbstract([],zeta)) ::
                              List.map (fun x -> OT (TVar x)) aas)))::
    bodyInstrs) in
  let retCode = HCode (DEpsilon epsilon :: DZeta zeta :: List.map (fun x -> DAlpha x) aas,
    ["r1", talResTy], SAbstract (raTy::transArgTys, zeta), QI 0,
    [(Isld (l,"ra", 0));
    Isfree (l, List.length xts + 1);
    Iret (l, "ra", "r1")]) in
  let heap = (retLoc, retCode)::bodyHeap in
  let heapTy = (retLoc, PBlock (DEpsilon epsilon :: DZeta zeta :: List.map (fun x -> DAlpha x) aas,
    ["r1", talResTy], SAbstract (raTy::transArgTys, zeta), QI 0))::bodyHeapTy in  
  (h, heap, heapTy)
| A.HTuple (l, vals) -> 
  let tvals = optionMap compileValue vals in
  (HTuple tvals, [], [])
(* | HInl val -> ...
| HInr val -> ... *)  
and compileExpr initialHeapTy aas argStack body zeta epsilon retmark = raise (Failure "TODO")
