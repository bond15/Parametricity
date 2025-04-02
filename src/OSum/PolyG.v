Require Import Autosubst.Autosubst.


Module PolyG.
(* PolyC would add TTag : type *)
Inductive type :=
    | TDyn : type
    | TVar (x : var)
    | TUnit
    | TBool : type
    | TProd (x y : type)
    | TArrow (x y : type)
    | TExistNew (x : {bind type})
    | TForallNew (x : {bind type}).

Inductive groundTy := 
    | GVar 
    | GBool 
    | GProd 
    | GArr 
    | GExist 
    | GForall.

Inductive expr := 
    | Var (x : var)
    | Ascript (e : expr)(t : type)
    | Seal (t : type)(e : expr)
    | Unseal (t : type)(e : expr)
    | TagTest (g : groundTy) (e : expr)
    | Let (e1 : expr) (e2 : {bind expr})
    | Bool (b : bool)
    | If (e1 e2 e3 : expr)
    | Pair (e1 e2 : expr)
    | PairElim (e1 : expr)(e2 : {bind (expr * expr)})
    | Lam (e : {bind expr})
    | App (e1 e2 : expr)
    | Pack (e : expr)
    | Unpack (e1 : expr)(e2 : {bind expr})
    | TLam (e : expr)
    | TApp (e1 : expr)(e2 : {bind expr}).


End PolyG.