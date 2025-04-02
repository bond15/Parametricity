
From MyProject.src.SystemF Require Export typing.
From MyProject.src.OSum Require Export OSum PolyG.

Module translation.

    Module F := typing.
    Module G := PolyG.

    Fixpoint ty (t : F.type) : G.type := 
        match t with 
        | F.TUnit => G.TBool
        | F.TBool => G.TBool
        | F.TInt => G.TBool
        | F.TProd t1 t2 => G.TProd (ty t1) (ty t2)
        | F.TSum t1 t2 => G.TBool
        | F.TArrow t1 t2 => G.TArrow (ty t1) (ty t2)
        | F.TVar x => G.TVar x
        | F.TForall t => G.TForallNew (ty t)
        | F.TExist t => G.TExistNew (ty t)
        end.

    

End translation.