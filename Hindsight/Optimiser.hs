module Hindsight.Optimiser where

import MinHS.Syntax(Op(..),TyCon(..))
import Hindsight.Syntax
import Data.List
import Text.Printf
import Debug.Trace


optimiser :: CBind -> CBind
optimiser (CBind x ty args e) = CBind x ty args (optimiseC e)


-- False means that id is illigally referenced
-- True  means that id is defined and then referenced
                    -- or not referenced at all
isBounded :: Id -> CExp -> Bool
isBounded id cexpr = 
    case cexpr of
        ref@(Produce x) -> 
            case x of 
                (Var name) -> not (name == id)
                (Thunk cexprInner) -> isBounded id cexprInner
                _ -> True

        ref@(Force x) -> 
            case x of 
                (Var name) -> not (name == id)
                (Thunk cexprInner) -> isBounded id cexprInner
                _ -> True

        ref@(Reduce id1 cexprInner cexprInner2) -> 
            isBounded id cexprInner
            &&
            (
                id1 == id 
                || 
                isBounded id cexprInner2
            )

        ref@(Let vbinds cexprInner) -> 
            all (== True) (map (\(VBind id1 _ vexprInner) -> 
                                case vexprInner of 
                                    (Var name)          -> not (name == id)
                                    (Thunk cexprInner2)  -> isBounded id cexprInner2
                                    _ -> True
                                ) vbinds
                          )
            &&
            (
                (id `elem` map (\(VBind id1 _ _) -> id1) vbinds) 
                ||
                isBounded id cexprInner
            )

        ref@(App cexprInner vexprInner) -> 
            let 
                newV = case vexprInner of
                        (Var name) -> not (name == id)
                        (Thunk cexprInner2)  -> isBounded id cexprInner2
                        _ -> True

                newC = isBounded id cexprInner
            in
                newV && newC
        
        ref@(Recfun (CBind fname ftype params cexprInner)) -> 
            id `elem` params
            ||
            isBounded id cexprInner

        ref@(If vexprInner cexprInner cexprInner2) ->
            let 
                newV = case vexprInner of
                        (Var name) -> not (name == id)
                        (Thunk cexprInner2)  -> isBounded id cexprInner2
                        _ -> True

                newC = isBounded id cexprInner
                newC2 = isBounded id cexprInner2
            in
                newV && newC && newC2
            
        _ -> 
            trace (show cexpr)
            True


substitute :: Id -> VExp -> CExp -> CExp
substitute id vexpr cexpr = 
    case cexpr of
        ref@(Produce x) -> 
            case x of 
                (Var name) -> 
                    if name == id then
                        Produce vexpr
                    else 
                        ref

                (Thunk cexprInner) -> 
                    Produce $ Thunk $ substitute id vexpr cexprInner

                _ -> ref

        ref@(Force x) -> 
            case x of 
                (Var name) -> 
                    if name == id then
                        Force vexpr
                    else 
                        ref

                (Thunk cexprInner) -> 
                    Force $ Thunk $ substitute id vexpr cexprInner
                
                _ -> ref

        ref@(Reduce id1 cexprInner cexprInner2) -> 
            let 
                newC1 = substitute id vexpr cexprInner
                newC2 = if id1 /= id then
                            substitute id vexpr cexprInner2
                        else
                            cexprInner2
            in 
                Reduce id1 newC1 newC2


        ref@(Let vbinds cexprInner) -> 
            let 
                newVbinds = map (\(VBind id1 vtype vexprInner) -> 
                                    let 
                                        newVexpr = case vexprInner of 
                                                        (Var name) -> 
                                                            if name == id then
                                                                vexpr
                                                            else 
                                                                vexprInner

                                                        (Thunk cexprInner) -> 
                                                            Thunk (substitute id vexpr cexprInner)

                                                        _ -> vexprInner
                                    in
                                        VBind id1 vtype newVexpr
                                ) vbinds
                newCexpr = 
                    if id `elem` map (\(VBind id1 _ _) -> id1) vbinds then
                        cexprInner
                    else
                        substitute id vexpr cexprInner
            in
                Let newVbinds newCexpr

        ref@(App cexprInner vexprInner) -> 
            let 
                newV = case vexprInner of
                            (Var name) -> 
                                if name == id then
                                    vexpr
                                else 
                                    vexprInner

                            (Thunk cexprInner) -> 
                                Thunk (substitute id vexpr cexprInner)
                            
                            _ -> vexprInner


                newC = substitute id vexpr cexprInner
            in
                App newC newV
        
        ref@(Recfun (CBind fname ftype params cexprInner)) -> 
            if id `elem` params then
                ref
            else
                let 
                    newC = substitute id vexpr cexprInner
                in 
                    Recfun (CBind fname ftype params newC)

        ref@(If vexprInner cexprInner cexprInner2) ->
            let 
                newV = case vexprInner of
                        (Var name) -> 
                            if name == id then
                                vexpr
                            else 
                                vexprInner

                        (Thunk cexprInner) -> 
                            Thunk (substitute id vexpr cexprInner)

                        _ -> vexprInner

                newC = substitute id vexpr cexprInner
                newC2 = substitute id vexpr cexprInner2
            in
                If newV newC newC2
            
        _ -> 
            cexpr

        

optimiseC :: CExp -> CExp
optimiseC (Force (Thunk v)) = v
optimiseC (Reduce name (Produce x) cexpr) = 
    optimiseC $ substitute name x cexpr
optimiseC ref@(App (Recfun (CBind id ctype [param] cexpr)) vexpr) = 
    -- If id not in FV(ref)
    if isBounded id cexpr then 
        optimiseC $ substitute param vexpr cexpr
    else 
        App (Recfun (CBind id ctype [param] (optimiseC cexpr))) vexpr

optimiseC c = 
    case c of  
        Produce x ->  Produce $
            case x of 
                (Thunk cexprInner) -> 
                    Thunk $ optimiseC cexprInner
                _ -> x

        Force x -> Force $
            case x of 
                (Thunk cexprInner) -> 
                    Thunk $ optimiseC cexprInner
                _ -> x

        Reduce id cexprInner cexprInner2 ->
            let 
                newC1 = optimiseC cexprInner
                newC2 = optimiseC cexprInner2
            in 
                Reduce id newC1 newC2


        Let vbinds cexprInner ->
            let 
                newVbinds = map (\(VBind id1 vtype vexprInner) -> 
                                    let 
                                        newVexpr = case vexprInner of 
                                                        (Thunk cexprInner2) -> 
                                                            Thunk (optimiseC cexprInner2)
                                                        _ -> vexprInner
                                    in
                                        VBind id1 vtype newVexpr
                                ) vbinds
                newCexpr = optimiseC cexprInner
            in
                Let newVbinds newCexpr

        App cexprInner vexprInner ->
            let 
                newV = case vexprInner of
                            (Thunk cexprInner2) -> 
                                Thunk (optimiseC cexprInner2)
                            _ -> vexprInner
                newC = optimiseC cexprInner
            in
                App newC newV
        
        Recfun (CBind fname ftype params cexprInner) ->
            let 
                newC = optimiseC cexprInner
            in 
                Recfun (CBind fname ftype params newC)

        If vexprInner cexprInner cexprInner2 ->
            let 
                newV = case vexprInner of
                        (Thunk cexprInner3) -> 
                            Thunk (optimiseC cexprInner3)
                        _ -> vexprInner

                newC = optimiseC cexprInner
                newC2 = optimiseC cexprInner2
            in
                If newV newC newC2
            
        _ -> c

optimiseC c = 
    trace (show c)
    $
    error "TODO: implement optimiseC"
