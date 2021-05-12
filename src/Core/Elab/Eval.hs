{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Strict            #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards  #-}
{-# LANGUAGE PatternSynonyms  #-}

module Core.Elab.Eval where

-- tartlet
import Core.Expression
import Core.Elab.Value

-- mtl
import Control.Monad.Except
-- Note: test strict vs lazy
import Control.Monad.State

-- containers
import qualified Data.IntMap as IntMap
import Data.IntMap ( IntMap )


-- base
import Data.Bifunctor

data ElabError = ElabError
data UnifyError =
    UnifyError Expr Expr
  | OccursCheck
  | VariableError
  | ScopeError
  | SpineError
  | ConvError Value Value
  | TopLevelNoType Name
  | InferError RawExpr

type MCtxt = IntMap Value


(?!) :: [a] -> Int -> Maybe a
(?!) l n = go l n
  where
    go [] _ = Nothing
    go (x : _) 0 = Just x
    go (_ : xs) i = go xs (i - 1)


-- To do add a reader for the topEnv to this
type ElabM m = StateT (Int, MCtxt) m


type Bind = Bool

pattern Bound :: Bind
pattern Bound   = True
pattern Defined :: Bind
pattern Defined = False

data Con = Con {
    localEnv      :: LocalEnv
  , depth         :: Int
  , bounds        :: [Bind]
  , typingContext :: [(Name, Ty)] -- Use strict pair
  }


emptyCon :: Con
emptyCon  = Con mempty 0 mempty mempty


bind :: Con -> Name -> Ty -> Con
bind (Con loc dep bds tys) nm ty =
  Con (VVar dep : loc) (dep + 1) (Bound : bds) ((nm, ty) : tys)


def :: Con -> Name -> Value -> Ty -> Con
def (Con loc dep bds tys) nm ~body ~ty =
  Con (body : loc) (dep + 1) (Defined : bds) ((nm, ty) : tys)


{-# INLINE appClos #-}
appClos :: MCtxt -> TopEnv -> Closure -> Value -> Value
appClos metaC topEnv (Closure locEnv expr) val = eval metaC topEnv (val : locEnv) expr


-- Take a metacontext and if the value is a meta-headed spine
-- then see if the variable is solved and if so apply the
-- the solution.
force :: MCtxt -> TopEnv -> Value -> Value
force metaC topEnv = \case
  VNeutral (NSpine (HMeta m) sp) | Just t <- IntMap.lookup m metaC ->
                      -- the spine is in reverse order
                      -- meta [spn, .. sp1]  ~> force meta [spn_1 ... sp1] `apply` spn
      force metaC topEnv (foldr (flip (doApply metaC topEnv)) t sp)
  v -> v

-- Perform force inside Elab monad.
forceM :: Monad m => TopEnv -> Value -> ElabM m Value
forceM topEnv v =
  gets (\(_, mCtxt) -> force mCtxt topEnv v)
  
-- For now conv' does a full readback of values and then checks for equality.
-- There is probably a better way to do this where we only read back those values
-- that are necessary and take shortcuts on equality of glued values unfolding only
-- when needed.
conv' :: MCtxt -> TopEnv -> Value -> Value -> Bool
conv' metaC topEnv val1 val2 =
  let
    e1 = readBackExpr True metaC topEnv 0 val1
    e2 = readBackExpr True metaC topEnv 0 val2
  in
    e1 == e2

    
-- In our syntax we use de-bruijn indices but in our evaluator we use de-bruijn levels,
-- this means the eval function uses indices but the readback uses levels.     
eval :: MCtxt -> TopEnv -> LocalEnv -> Expr -> Value
eval metaC topEnv locEnv =
  let
    localEval = eval metaC topEnv locEnv
    vClos loc body = Closure loc body
  in
  \case
    (Prim p) -> evalPrim p
    (PrimBinOp op e1 e2) -> evalPrimBinOp op (localEval e1) (localEval e2)
    (PrimTy pTy) -> VPrimTy pTy
    (Loc v) -> evalLocVar locEnv v
    (Top v) -> evalTopVar topEnv v
    (Pi n dom dep) -> VPi n (localEval dom) (vClos locEnv dep)
    (Lam n body) -> VLam n (vClos locEnv body)
    (Let _ val body) -> eval metaC topEnv (extendEnv locEnv (localEval val)) body
    (App fn arg) -> doApply metaC topEnv (localEval fn) (localEval arg)
    (Sigma a carT cdrT) ->
      VSigma a (localEval carT) (vClos locEnv cdrT)
    (Cons f s) -> VPair (localEval f) (localEval s)
    (Car p) -> doCar (localEval p)
    (Cdr p) -> doCdr (localEval p)
    Nat -> VNat
    Zero -> VZero
    (Add1 n) -> VAdd1 (localEval n)
    (IndNat tgt mot base step)
      -> doIndNatStep
           metaC
           topEnv
           (localEval tgt)
           (localEval mot)
           (localEval base)
           (localEval step)
    (Equal ty from to)
      -> VEqual (localEval ty) (localEval from) (localEval to)
    Same -> VSame
    (Replace eq mot base) ->
      doReplace (localEval eq) (localEval mot) (localEval base)
    Trivial -> VTrivial
    Sole -> VSole
    Absurd -> VAbsurd
    (IndAbsurd false ty) -> doIndAbsurd (localEval false) (localEval ty)
    Atom -> VAtom
    (Tick chrs) -> VTick chrs
    U -> VU
    (The _ e) -> localEval e
    Meta m -> evalMetaVar metaC m
    InsertedMeta meta bds ->
      doApplyBds metaC topEnv locEnv (evalMetaVar metaC meta) bds


evalM :: (Monad m) => Ctxt -> Expr -> ElabM m Value
evalM (topEnv, locEnv) expr = gets (\(_, ms) -> eval ms topEnv locEnv expr)

evalPrim :: Prim -> Value
evalPrim = VPrim


evalPrimBinOp :: PrimBinOp -> Value -> Value -> Value
evalPrimBinOp PAddI (VPrim (PInt n1)) (VPrim (PInt n2)) =
  VPrim (PInt (n1 + n2))
evalPrimBinOp op (VNeutral neu1) ~v2 =
  VNeutral (NPrimBinOp op neu1 v2)
evalPrimBinOp _ ~v1 ~v2 =
  tyCheckError "evalPrimBinOpError" [v1, v2]


evalLocVar :: LocalEnv -> Int -> Value
evalLocVar locEnv depth =
  maybe (VVar depth) id $ locEnv ?! depth 


evalMetaVar :: MCtxt -> Int -> Value
evalMetaVar metaSub meta =
  maybe (VMeta meta) id $ meta `IntMap.lookup` metaSub


evalTopVar :: TopEnv -> Name -> Value
evalTopVar topEnv name =
  let
    ~normal = (maybe (lookupTopError "evalTopVar" name) id $ lookup name topEnv)
    ~val    = normalVal normal
    ~ty     = normalTy  normal
    spine   = []
  in
    VTop name spine ty val

lookupTopError :: String -> Name -> Normal
lookupTopError funName name = error $
  unlines
    [ "Internal error (" <> funName <> "): lookupError"
    , show name
    ]

lookupVarError :: String -> Int -> Value
lookupVarError funName name = error $
  unlines
    [ "Internal error (" <> funName <> "): lookupError"
    , show name
    ]


tyCheckError :: String -> [Value] -> Value
tyCheckError funName _ = error $
  unlines $
    [ "Internal error (" <> funName <> "): typecheckerError"
    ]

doApply  :: MCtxt -> TopEnv -> Value -> Value -> Value
doApply metaC topEnv (VLam _ fn) ~arg = appClos metaC topEnv fn arg
doApply _ _ (VNeutral (NSpine h sp)) ~arg =
    VNeutral (NSpine h (arg : sp))
doApply metaC topEnv (VTop var sp (VPi _ _ depT) val) ~arg =
  let
    subDepT = appClos metaC topEnv depT arg
    spine'  = (arg : sp)
  in
    VTop var spine' subDepT (doApply metaC topEnv val arg)
doApply _ _ fun arg = tyCheckError "doApply metaC topEnv" [fun, arg]


doApplyBds :: MCtxt -> TopEnv -> LocalEnv -> Value -> [Bind] -> Value
doApplyBds metaC topEnv locEnv ~v bounds = go (locEnv, bounds)
  where
    go :: ([Value], [Bind]) -> Value
    go =
      let
        locApp = doApply metaC topEnv
      in
      \case
        ([], []) -> v
        (bdV : lEnv, Bound   : bds) -> go (lEnv, bds) `locApp` bdV
        (_   : lEnv, Defined : bds) -> go (lEnv, bds)
        _ -> error "doApplyBds: ctxt error"



doCar :: Value -> Value
doCar (VPair f _) = f
doCar (VNeutral neu) = VNeutral (NCar neu)
doCar val = tyCheckError "doCar" [val]


doCdr :: Value -> Value
doCdr (VPair _ s) = s
doCdr (VNeutral neu) =
    VNeutral (NCdr neu)
doCdr val = tyCheckError "doCdr" [val]


doIndAbsurd :: Value -> Value -> Value
doIndAbsurd (VNeutral neu) mot =
  VNeutral (NIndAbsurd neu mot)
doIndAbsurd v mot = tyCheckError "doIndAbsurd" [v, mot]


doReplace :: Value -> Value -> Value -> Value
doReplace VSame _ base = base
doReplace (VNeutral neu) mot base =
    VNeutral (NReplace neu mot base)
doReplace eq mot base = tyCheckError "doReplace" [eq, mot, base]


doIndNatStep :: MCtxt -> TopEnv -> Value -> Value -> Value -> Value -> Value
doIndNatStep _ _ VZero _ base _ = base
doIndNatStep metaC topEnv (VAdd1 nV) mot base step =
  doApply metaC topEnv (doApply metaC topEnv step nV) (doIndNatStep metaC topEnv nV mot base step)
doIndNatStep _ _ (VNeutral neu) mot base step =
    VNeutral
      (NIndNat neu
        mot
        base
        step
      )
doIndNatStep _ _ nVal mot base step = tyCheckError "doIndNatStep" [nVal, mot, base, step]


-- Here the depth refers to a variable which is not under any binder,
-- this starts at 1 and increases as we pass under any binder. This gives us a source of fresh variables.
readBackExpr :: Bool -> MCtxt -> TopEnv -> Int -> Value -> Expr
readBackExpr unf metaC topEnv depth val = go depth val
  where
  go :: Int -> Value -> Expr
  go d v =
    let
      localReadNeu = readBackNeutral unf metaC topEnv d
      localAppClos = appClos metaC topEnv
      localDoApply = doApply metaC topEnv
      fresh = d + 1
    in
    case force metaC topEnv v of
        VZero -> Zero
        VAdd1 nV -> Add1 (go d nV)
        VTop topVar sp _ topV ->
          if unf then
            go d topV
          else
            readBackSpine unf metaC topEnv (Top topVar) sp
        fun@(VLam name _) ->
          let
            varV = VNeutral (NVar fresh)
          in
            Lam name $
              go fresh (localDoApply fun varV)
        VPair carV cdrV ->
          Cons
          (go d carV)
          (go d cdrV)
        VSole -> Sole
        VSame -> Same
        VNat     -> Nat
        VTrivial -> Trivial
        VAbsurd  -> Absurd
        VAtom    -> Atom
        VTick chars -> Tick chars
-- This needs to change when universes are added
        VU -> U
        VEqual t from to ->
          Equal
          (go d t)
          (go d from)
          (go d to)
        VSigma n carT cdrT ->
         let
           varV  = VNeutral (NVar fresh)
           cdrV  = localAppClos cdrT varV
           cdrTFin = go fresh cdrV
           carTFin = go d carT
         in
           Sigma n carTFin cdrTFin
        VPi n domT depT ->
         let
           varV  = VNeutral (NVar fresh)
           domTFin = go d domT
           depTV = appClos metaC topEnv depT varV
           depTFin = go fresh depTV
         in
          Pi n domTFin depTFin
        VNeutral neu -> localReadNeu neu
        vE -> readBackError "readBackTyped" vE

level2Index :: DBLvl -> DBLvl -> DBInd
level2Index depth l = depth - l - 1

readBackSpine :: Bool -> MCtxt -> TopEnv -> Expr -> Spine -> Expr
readBackSpine = undefined

readBackNeutral :: Bool -> MCtxt -> TopEnv -> DBLvl -> Neutral -> Expr
readBackNeutral unf metaC topEnv depth =
  let
    localReadNeutral = readBackNeutral unf metaC topEnv depth
    localReadExpr    = readBackExpr unf metaC topEnv depth
  in \case
               -- Convert debruijn level to debruijn index
  (NSpine h sp) ->
    let
      hdN = case h of
        HMeta m -> Meta m
        HVar  i -> Loc $ level2Index depth i
        HTop  n -> Top n
    in
      foldr
        (\ ~val acc -> App acc (localReadExpr val))
        hdN
        sp
  (NPrimBinOp op neu norm) ->
    PrimBinOp op (localReadNeutral neu) (localReadExpr norm)
  (NCar neu) -> Car (localReadNeutral neu)
  (NCdr neu) -> Cdr (localReadNeutral neu)
  (NIndNat n mot base step) ->
    IndNat
      (localReadNeutral n)
      (localReadExpr mot)
      (localReadExpr base)
      (localReadExpr step)
  (NReplace eq mot base) ->
    Replace
      (localReadNeutral eq)
      (localReadExpr mot)
      (localReadExpr base)
  (NIndAbsurd absurd ty) ->
    IndAbsurd
      (The Absurd (localReadNeutral absurd))
      (localReadExpr ty)


readBackError :: String -> Value -> Expr
readBackError funName _ = error $
  unlines $
    [ "Internal error (" <> funName <> "): typecheckerError"
    ]

fullyUnfold :: Bool
fullyUnfold = True

noUnfold :: Bool
noUnfold = False

data PartialRename = PartialRename
  { domL :: Int
  , codL :: Int
  , ren  :: IntMap Int
  }

extPR :: PartialRename -> PartialRename
extPR (PartialRename lenD lenR ren)
  = PartialRename (lenD + 1) (lenR + 1) (IntMap.insert lenR lenD ren)

invert :: forall m . (MonadError UnifyError m) => TopEnv -> Int -> [Value] -> ElabM m PartialRename
invert topEnv gamma spine = do
  (dom, ren) <- go spine
  pure $ PartialRename dom gamma ren
  where
    go :: [Value] -> ElabM m (Int, IntMap Int)
    go [] = pure (0, mempty)
    go (t : sp) = do
      (domL, ren) <- go sp
      tV <- forceM topEnv t
      case tV of
        VVar i | IntMap.notMember i ren -> pure (domL + 1, IntMap.insert i domL ren)
        _ -> throwError VariableError


rename
  :: forall m . (MonadError UnifyError m)
  => TopEnv -> Int -> PartialRename -> Value -> ElabM m Expr
rename topEnv meta partialRename v = go partialRename v
  where
  goSp :: PartialRename -> Expr -> [Value] -> ElabM m Expr
  goSp _  t [] = pure t
  goSp pr t (u : sp) = App <$> goSp pr t sp <*> go pr u
    
  go :: PartialRename -> Value -> ElabM m Expr
  go pr t = do
    (_, metaC) <- get
    tV <- forceM topEnv t
    let localAppClos = appClos metaC topEnv
    case tV of
      VMetaSp meta' sp | meta == meta' -> throwError OccursCheck
                       | otherwise     -> goSp pr (Meta meta') sp

      VLam n clos -> Lam n <$> go (extPR pr) (localAppClos clos (VVar (codL pr)))
                                       -- We apply the codL variable
                                       -- as the term we are renaming will
                                       -- live under that many lambdas
                                       -- and we are using levels.
      VSigma n ty clos ->
        Sigma n
          <$> go pr ty
          <*> go (extPR pr) (localAppClos clos (VVar (codL pr)))
      VPi n ty clos ->
        Pi n
          <$> go pr ty
          <*> go (extPR pr) (localAppClos clos (VVar (codL pr)))          
          
      VPair car cdr -> Cons <$> (go pr car) <*> (go pr cdr)
      VNat -> pure Nat
      VZero -> pure Zero
      VPrim p -> pure $ Prim p
      VPrimTy pTy -> pure $ PrimTy pTy
      VAdd1 nat -> Add1 <$> go pr nat
      VEqual ty from to -> Equal <$> (go pr ty) <*> (go pr from) <*> (go pr to)
      VSame -> pure Same
      VTrivial -> pure Trivial
      VSole -> pure Sole
      VAbsurd -> pure Absurd
      VAtom -> pure Atom
      VTick chrs -> pure $ Tick chrs
      VU -> pure U
      VTop name _ _ _ -> pure (Top name)
      VNeutral neu -> goNeu pr neu

  goNeu :: PartialRename -> Neutral -> ElabM m Expr
  goNeu pr = \case
    NSpine (HTop n) sp -> goSp pr (Top n) sp
    NSpine (HVar i) sp -> case IntMap.lookup i (ren pr) of
      Just i' -> goSp pr (Var $ level2Index (domL pr) i') sp
      Nothing -> throwError ScopeError
    NSpine (HMeta meta') _  | meta == meta' -> throwError OccursCheck
    NSpine (HMeta meta') sp | otherwise -> goSp pr (Meta meta') sp
            
    NPrimBinOp op neu norm ->
      PrimBinOp op
        <$> goNeu pr neu
        <*> go pr norm
    NCar neu' -> Car <$> goNeu pr neu'
    NCdr neu' -> Cdr <$> goNeu pr neu'
    NIndNat neu' norm1 norm2 norm3 ->
      IndNat
        <$> (goNeu pr neu')
        <*> go pr norm1
        <*> go pr norm2
        <*> go pr norm3
    NReplace neu' norm1 norm2 ->
      Replace
        <$> (goNeu pr neu')
        <*> go pr norm1
        <*> go pr norm2
    NIndAbsurd neu' norm ->
      IndAbsurd
        <$> (goNeu pr neu')
        <*> go pr norm


quoteM :: (Monad m) => TopEnv ->  Bool -> Int -> Value -> ElabM m Expr
quoteM topEnv unf depth val =
  gets $ \ (_, metaC) -> readBackExpr unf metaC topEnv depth val

valueToString :: Value -> String
valueToString = undefined


unfoldTopVar :: TopEnv -> Name -> Expr
unfoldTopVar topEnv n =
  let
    readBack = readBackExpr fullyUnfold mempty topEnv 0
  in
    readBack (evalTopVar topEnv n)



-- Wrap a term in lambdas up to the current depth
lams :: Int -> Expr -> Expr
lams depth = go 0
  where
    go i t | i == depth = t
    go i t = Lam (newVar <> show i) $ go (i + 1) t

solve
  :: (MonadError UnifyError m)
  => TopEnv -> Int -> Meta -> [Value] -> Value -> ElabM m ()
solve topEnv depth meta sp rhsV = do
  pr <- invert topEnv depth sp
  renamedRHS <- rename topEnv meta pr rhsV
  solution <- evalM (topEnv, mempty) $ lams (domL pr) renamedRHS
  modify' (second $ IntMap.insert meta solution)


unify :: forall m . (MonadError UnifyError m)
  => Int -> TopEnv -> Value -> Value -> ElabM m ()
unify d topEnv = go d where
  go :: Int -> Value -> Value -> ElabM m ()
  go depth lhs rhs = do
    metaC <- gets snd
    let localAppClos = appClos metaC topEnv
    let localDoApply = doApply metaC topEnv
    case (force metaC topEnv lhs, force metaC topEnv rhs) of
      (VLam _ body1, VLam _ body2) ->
        let
          varV = VVar depth
          body1' = localAppClos body1 varV
          body2' = localAppClos body2 varV
        in
          go (depth + 1) body1' body2'
      (VLam _ body1, f2) ->
        let
          depth' = depth + 1
          varV = VVar depth
        in
          go depth' (localAppClos body1 varV) (localDoApply f2 varV)
      (f1, VLam _ body2) ->
        let
          depth' = depth + 1
          varV   = VVar depth
        in
          go depth' (localAppClos body2 varV) (localDoApply f1 varV) 
      (VSigma _ dom1T dep1T, VSigma _ dom2T dep2T) ->
        let
          depth' = depth + 1
          varV  = VVar depth
        in
          go depth dom1T dom2T >>
          go depth' (localAppClos dep1T varV) (localAppClos dep2T varV)
      (VPi _ dom1T dep1T, VPi _ dom2T dep2T) ->
        let
          depth' = depth + 1
          varV  = VVar depth
        in
          go depth dom1T dom2T >>
          go depth' (localAppClos dep1T varV) (localAppClos dep2T varV)  
      (VPair car1 cdr1, VPair car2 cdr2) ->
        go depth car1 car2 >>
        go depth cdr1 cdr2
      (VNeutral (NSpine hd1 sp1), VNeutral (NSpine hd2 sp2))
        | hd1 == hd2 -> goSp depth sp1 sp2
      (VNeutral (NSpine (HMeta m1) sp1), f2) ->
        solve topEnv depth m1 sp1 f2
      (f1, VNeutral (NSpine (HMeta m2) sp2)) ->
        solve topEnv depth m2 sp2 f1
      (VEqual ty1 from1 to1, VEqual ty2 from2 to2) ->
        go depth ty1 ty2     >>
        go depth from1 from2 >>
        go depth to1 to2
      (cstr1, cstr2) | cmpConstrs cstr1 cstr2 == True -> pure ()
      (t1, t2) -> do
        t1N <- quoteM topEnv True depth t1
        t2N <- quoteM topEnv True depth t2
        throwError $ UnifyError t1N t2N

  goSp :: Int -> [Value] -> [Value] -> ElabM m ()
  goSp depth sp1 sp2 = case (sp1, sp2) of
    ([], []) -> pure ()
    (u1 : sp1' , u2 : sp2') ->
      goSp depth sp1' sp2' >>
      go depth u1 u2
    (_, _) -> throwError SpineError
      

freshMeta
  :: (Monad m)
  => Con -> ElabM m Expr
freshMeta ctxt = do
  (meta, _) <- get
  modify' (first (+ 1))
  pure $ InsertedMeta meta (bounds ctxt)

check :: forall m . (Monad m, MonadError UnifyError m) =>
  TopEnv -> Con -> RawExpr -> Ty -> ElabM m Expr
check topEnv ctxt = go (depth ctxt) ctxt
  where

    go :: Int -> Con -> RawExpr -> Ty -> ElabM m Expr
    go depth con exprR ty = do
      let evalCon = (topEnv, localEnv con)
      (_, metaC) <- get
      let localAppClos = appClos metaC topEnv
      tySolved <- forceM topEnv ty
      case (exprR, tySolved) of
        (LamR n body, VPi _ domT depT) -> do
          let
            varV = VVar depth
            depth' = depth + 1
            tyEnv' = bind con n domT -- extendTyEnv tyEnv domT          
          Lam n <$> go depth' tyEnv' body (localAppClos depT varV)
        (ConsR carR cdrR, VSigma _ domT depT) -> do
          carE <- go depth con carR domT
          carV <- evalM evalCon carE
          go depth con cdrR (localAppClos depT carV)
        (SameR, VEqual _ from to) -> do
          unless (conv' metaC topEnv from to)
            (throwError $ ConvError from to)
          pure Same
        (PrimR p@(PInt _), VPrimTy PTyInt) -> do
          pure $ Prim p
        (HoleR, _) ->
          freshMeta con
        _ -> do
          (expr, exprTyV) <- synth topEnv con exprR
          unify depth topEnv exprTyV tySolved 
          pure expr


freshClos1 :: (Monad m) => TopEnv -> Con -> ElabM m (Ty, Closure)
freshClos1 topEnv ctxt = do
  dom <- freshMeta ctxt
  ~domV <- evalM (topEnv, []) dom
  dep <- freshMeta (bind ctxt metaVar domV)
  let ~depCl = Closure [domV] dep
  pure (domV, depCl)

indNatStepType :: Value -> Value
indNatStepType mot =
-- could write this out explicitly?
  eval mempty [] [mot]
    (Pi "n-1" Nat
      (Pi "ind"
         (App (Loc 2) (Loc 1))
         (App (Loc 2) (Add1 (Loc 1))
         )
      )
    )


indNatMot :: Value
indNatMot =
  eval mempty [] [] $ Pi "n" Nat U

synth ::
  forall m . (Monad m, MonadError UnifyError m)
  => TopEnv -> Con -> RawExpr -> ElabM m (Expr, Ty)
synth topEnv context = go 0 context
  where
    go :: Int -> Con -> RawExpr -> ElabM m (Expr, Ty)
    go depth ctxt =
      let
        evalCon = (topEnv, localEnv ctxt)
        -- to do: use localUnify
      in
      \case
        LocR nm ->
          let
            getDBInd :: DBInd -> [(Name, Ty)] -> ElabM m (Expr, Ty)
            getDBInd ind ((nm', ty) : _) | nm == nm' =  pure (Loc ind, ty)
            getDBInd ind (_ : tys) = getDBInd (ind + 1) tys
            getDBInd _  _ = throwError ScopeError
          in
            getDBInd 0 (typingContext ctxt)

        UnivR -> pure (U, VU)
        TickR chrs -> pure (Tick chrs, VAtom)
        AtomR   -> pure (Atom, VU)
        AbsurdR -> pure (Absurd, VU)
        SoleR   -> pure (Sole, VTrivial)
        UnitR   -> pure (Trivial, VU)
        ZeroR   -> pure (Zero, VNat)
        Add1R n -> do
          (nExpr, ty) <- go depth ctxt n
          unify depth topEnv ty VNat
          pure (Add1 nExpr, VNat)
        PrimBinOpR op arg1 arg2 -> do
          (arg1E, ty1) <- go depth ctxt arg1
          unify depth topEnv ty1 (VPrimTy PTyInt)
          (arg2E, ty2) <- go depth ctxt arg2
          unify depth topEnv ty2 (VPrimTy PTyInt)          
          pure (PrimBinOp op arg1E arg2E, VPrimTy PTyInt)          
        CarR pR -> do
          (pE, tyP) <- go depth ctxt pR
          (domT, depT) <- freshClos1 topEnv ctxt
          unify depth topEnv tyP (VSigma metaVar domT depT)
          pure (pE, domT)
        CdrR pR -> do
          metaC <- gets snd
          (pE, tyP) <- go depth ctxt pR
          (domT, depT) <- freshClos1 topEnv ctxt
          unify depth topEnv tyP (VSigma metaVar domT depT)
          let depSub = appClos metaC topEnv depT domT
          pure (pE, depSub)
        IndNatR tgt mot base step -> do
          metaC <- gets snd
          (tgtE, tgtTy) <- go depth ctxt tgt
          tgtV <- evalM evalCon tgtE
          unify depth topEnv tgtTy VNat
          (motE, motTy) <- go depth ctxt mot
          motV <- evalM evalCon motE
          unify depth topEnv motTy indNatMot
          (baseE, baseTy) <- go depth ctxt base
          unify depth topEnv baseTy (doApply metaC topEnv motV VZero)
          (stepE, stepTy) <- go depth ctxt step
          unify depth topEnv stepTy (indNatStepType motV)
          pure (IndNat tgtE motE baseE stepE, doApply metaC topEnv stepTy tgtV)
        PiR n domR depR -> do
          (domE, domTy) <- go depth ctxt domR
          unify depth topEnv domTy VU
          let ctxt' = bind ctxt n VU
          let depth' = depth + 1
          (depE, depTy) <- go depth' ctxt' depR
          unify depth topEnv depTy VU
          pure (Pi n domE depE, VU)
        SigmaR n domR depR -> do
          (domE, domTy) <- go depth ctxt domR
          unify depth topEnv domTy VU
          let ctxt' = bind ctxt n VU
          let depth' = depth + 1
          (depE, depTy) <- go depth' ctxt' depR
          unify depth topEnv depTy VU
          pure (Pi n domE depE, VU)
        AppR funR argR -> do
          metaC <- gets snd
          (funE, funTy) <- go depth ctxt funR
          funTySol <- forceM topEnv funTy
          (domV, depV) <-
            case funTySol of
              VPi _ domT depT -> pure (domT, depT)
              _ -> do
                (domT, depT) <- freshClos1 topEnv ctxt
                unify depth topEnv funTySol (VPi newVar domT depT)
                pure (domT, depT)
          argE <- check topEnv ctxt argR domV
          argV <- evalM evalCon argE
          pure (App funE argE, appClos metaC topEnv depV argV)
        LamR n bodyR -> do
          metaC <- gets snd
          domE  <- freshMeta ctxt
          domV  <- evalM evalCon domE
          (bodyE, bodyTy) <- go (depth + 1) (bind ctxt n domV) bodyR
          let bodyTyE = readBackExpr False metaC topEnv depth bodyTy
          pure (Lam n bodyE, VPi n domV (Closure (localEnv ctxt) bodyTyE))
        EqualR motR fromR toR -> do
          (motE, motTy) <- go depth ctxt motR
          motV <- evalM evalCon motE
          unify depth topEnv motTy VU
          (fromE, fromTy) <- go depth ctxt fromR
          unify depth topEnv fromTy motV
          (toE, toTy) <- go depth ctxt toR
          unify depth topEnv toTy motV
          pure (Equal motE fromE toE, VU)
        ReplaceR eqR motR baseR -> do
          metaC <- gets snd
          (eqE, eqTy) <- go depth ctxt eqR
          ty   <- freshMeta ctxt
          from <- freshMeta ctxt
          to   <- freshMeta ctxt
          eqMetaV <- evalM evalCon (Equal ty from to)
          unify depth topEnv eqTy eqMetaV
          motV <- evalM evalCon (Pi newVar ty U)
          motE <- check topEnv ctxt motR motV
          fromV <- evalM evalCon from
          toV   <- evalM evalCon to
          baseE <- check topEnv ctxt baseR (doApply metaC topEnv motV fromV)
          pure (Replace eqE motE baseE, doApply metaC topEnv motV toV)
        IndAbsurdR tgtR tyR -> do
          (tgtE, tgtTy) <- go depth ctxt tgtR
          unify depth topEnv tgtTy VAbsurd
          tyE <- check topEnv ctxt tyR VU
          tyV <- evalM evalCon tyE
          pure (IndAbsurd tgtE tyE, tyV)
        TheR exprR tyR -> do
          tyE   <- check topEnv ctxt tyR   VU
          tyV   <- evalM evalCon tyE
          exprE <- check topEnv ctxt exprR tyV
          pure (The exprE tyE, tyV)
        topR@(TopR n) -> case lookup n topEnv of
          Nothing -> throwError ScopeError
          Just norm ->
            let
              ty    = normalTy norm
            in
              do
                _ <- check topEnv ctxt topR ty
                pure (Top n, ty)
        restR -> do
          throwError $ InferError restR
