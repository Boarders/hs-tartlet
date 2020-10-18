{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Strict            #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards  #-}

module Core.Eval.Elab.Eval where

import Core.Expression
import Core.Eval.Elab.Value

import Control.Monad.Except
import qualified Data.IntMap as IntMap
import Data.IntMap ( IntMap )
-- Note: test strict vs lazy
import Control.Monad.State
import Data.Foldable
import Data.Bifunctor

data ElabError = ElabError
data UnifyError =
    UnifyError Expr Expr
  | OccursCheck
  | VariableError
  | ScopeError
  | SpineError Value
  | ConvError Value Value
  | TopLevelNoType Name

type MCtxt = IntMap Value
type BVar = Int

data Entry = B Value | Def Value

data ECtxt = ECtxt
  { eValues :: [Maybe Value]
  , eTypes  :: [Value]
  }

(?!) :: [a] -> Int -> Maybe a
(?!) l n = go l n
  where
    go [] _ = Nothing
    go (x : _) 0 = Just x
    go (_ : xs) i = go xs (i - 1)

eNil :: ECtxt
eNil = ECtxt [] []

-- To do add a reader for the topEnv to this
type ElabM m = StateT (Int, MCtxt) m

eBind :: Ty -> ECtxt -> ECtxt
eBind ty (ECtxt vals tys) = ECtxt (Nothing : vals) (ty : tys)


eDef :: Value -> Ty -> ECtxt -> ECtxt
eDef val ty (ECtxt vals tys) = ECtxt (Just val : vals) (ty : tys)


-- Take a metacontext and if the value is a meta-headed spine
-- then see if the variable is solved and if so apply the
-- the solution.
force :: MCtxt -> Value -> Value
force ms = \case
  VNeutral _ (NSpine (HMeta m) sp) | Just t <- IntMap.lookup m ms ->
    let
      sp' = fmap normalVal sp
    in
      force ms (foldr (flip doApply) t sp')
  v -> v

-- Perform force inside Elab monad.
forceM :: Monad m => Value -> ElabM m Value
forceM v =
  gets (\(_, mCtxt) -> force mCtxt v)
  
-- For now conv' does a full readback of values and then checks for equality.
-- There is probably a better way to do this where we only read back those values
-- that are necessary and take shortcuts on equality of glued values unfolding only
-- when needed.
conv' :: Ty -> Value -> Value -> Bool
conv' ty val1 val2 =
  let
    e1 = readBackTyped True mempty 0 (Just ty) val1
    e2 = readBackTyped True mempty 0 (Just ty) val2
  in
    e1 == e2
    
    
-- In our syntax we use de-bruijn indices but in our evaluator we use de-bruijn levels,
-- this means the eval function uses indices but the readback uses levels.     
eval :: MCtxt -> TopEnv -> LocalEnv -> Expr -> Value
eval metaSub topEnv locEnv =
  let
    localEval = eval metaSub topEnv locEnv
    binderEval loc body val = eval metaSub topEnv (extendEnv loc val) body
 -- abstract building a closure to switch from HOAS
    vClos loc body = \val -> binderEval loc body val
  in
  \case
    (Loc v) -> evalLocVar locEnv v
    (Top v) -> evalTopVar topEnv v
    (Pi n dom dep) -> VPi n (localEval dom) (vClos locEnv dep)
    (Lam n body) -> VLam n (vClos locEnv body)
    (App fn arg) -> doApply (localEval fn) (localEval arg)
    (Sigma a carT cdrT) ->
      VSigma a (localEval carT) (vClos locEnv cdrT)
    (Cons f s) -> VPair (localEval f) (localEval s)
    (Car p) -> doCar (localEval p)
    (Cdr p) -> doCdr (localEval p)
    Nat -> VNat
    Zero -> VZero
    (Add1 n) -> VAdd1 (localEval n)
    (IndNat tgt mot base step)
      -> doIndNatStep (localEval tgt) (localEval mot) (localEval base) (localEval step)
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
    Meta m -> evalMetaVar metaSub m


evalM :: (Monad m) => Ctxt -> Expr -> ElabM m Value
evalM (topEnv, locEnv) expr = gets (\(_, ms) -> eval ms topEnv locEnv expr)

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
    spine   = NTop name
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

doApply :: Value -> Value -> Value
doApply (VLam _ fn) ~arg = appClos fn arg
doApply (VNeutral (Just (VPi _ domT depT)) (NSpine h sp)) ~arg =
  let
    subDepT = appClos depT arg
    normArg = Normal (Just domT) arg
  in
    VNeutral (Just subDepT) (NSpine h (normArg : sp))
doApply (VTop v (NSpine h sp) (Just (VPi _ domT depT)) val) ~arg =
  let
    subDepT = appClos depT arg
    normArg = Normal (Just domT) arg
    nSpine  = NSpine h (normArg : sp)
  in
    VTop v nSpine (Just subDepT) (doApply val arg)
doApply fun arg = tyCheckError "doApply" [fun, arg]


doCar :: Value -> Value
doCar (VPair f _) = f
doCar (VNeutral (Just (VSigma _ domT _)) neu) = VNeutral (Just domT) (NCar neu)
doCar val = tyCheckError "doCar" [val]

doCdr :: Value -> Value
doCdr (VPair _ s) = s
doCdr neuV@(VNeutral (Just (VSigma _ _ depT)) neu) =
  let
    subDepT = appClos depT (doCar neuV)
  in
    VNeutral (Just subDepT) (NCdr neu)
doCdr val = tyCheckError "doCdr" [val]


doIndAbsurd :: Value -> Value -> Value
doIndAbsurd (VNeutral (Just VAbsurd) neu) mot =
  VNeutral (Just mot) (NIndAbsurd neu (Normal (Just VU) mot))
doIndAbsurd v mot = tyCheckError "doIndAbsurd" [v, mot]


doReplace :: Value -> Value -> Value -> Value
doReplace VSame _ base = base
doReplace (VNeutral (Just (VEqual ty from to)) neu) mot base =
  let
    transTgt = doApply mot to
    motT     = VPi "_" ty \_ -> VU
    baseT    = doApply motT from
  in
    VNeutral (Just transTgt) (NReplace neu (Normal (Just motT) mot) (Normal (Just baseT) base))
doReplace eq mot base = tyCheckError "doReplace" [eq, mot, base]


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

doIndNatStep :: Value -> Value -> Value -> Value -> Value
doIndNatStep VZero _ base _ = base
doIndNatStep (VAdd1 nV) mot base step =
  doApply (doApply step nV) (doIndNatStep nV mot base step)
doIndNatStep tgt@(VNeutral (Just VNat) neu) mot base step =
  let
    indT  = indNatStepType mot
    motT  = VPi "_" VNat \_ -> VU
    baseT = doApply mot VZero
  in
    VNeutral (Just $ doApply mot tgt)
      (NIndNat neu
       (Normal (Just motT) mot)
       (Normal (Just baseT) base)
       (Normal (Just indT) step)
      )
doIndNatStep nVal mot base step = tyCheckError "doIndNatStep" [nVal, mot, base, step]


readBackNormal :: Bool -> MCtxt -> Int -> Normal -> Expr
readBackNormal unf mctxt depth (Normal t v) = readBackTyped unf mctxt depth t v


-- Here the depth refers to a variable which is not under any binder, this starts at 1 and increases as we pass under any binder. This gives us a source of fresh variables.
readBackTyped :: Bool -> MCtxt -> Int -> (Maybe Ty) -> Value -> Expr
readBackTyped unf mctxt depth ty val = go depth (ty, val)
  where
  go :: Int -> (Maybe Ty, Value) -> Expr
  go d (tyM, v) =
    let
      localReadNeu = readBackNeutral unf mctxt d
      fresh = d + 1
    in
    case (tyM, force mctxt v) of
        (_, VZero) -> Zero
        (_,(VAdd1 nV)) -> Add1 (go d (Just VNat, nV))
        (topTy, (VTop _ sp _ topV)) ->
          if unf then
            go d (topTy, topV)
          else
            localReadNeu sp
        (Just (VPi _ domT depT), fun@(VLam name _)) ->
          let
            varV = VNeutral (Just domT) (NVar fresh)
          in
            Lam name $
              go fresh ((Just $ appClos depT varV), (doApply fun varV))
        (Nothing, fun@(VLam name _)) ->
          let
            varV = VNeutral Nothing (NVar fresh)
          in
            Lam name $
              go fresh (Nothing, (doApply fun varV))
        (Just (VSigma _ carT cdrT), pair) ->
          let
            carV = doCar pair
            cdrV = doCdr pair
            depT = appClos cdrT carV
          in
            Cons
              (go d ((Just carT), carV))
              (go d ((Just depT), cdrV))
        (Nothing, (VPair carV cdrV)) ->
          Cons
          (go d (Nothing, carV))
          (go d (Nothing, cdrV))
        (Just VTrivial, _) -> Sole
        (Nothing, VSole) -> Sole
        (_, (VNeutral (Just VAbsurd) neu)) ->
          The Absurd (localReadNeu neu)
        (_, VSame) -> Same
        (_, VTick chars) -> Tick chars
        (_, VNat)     -> Nat
        (_, VTrivial) -> Trivial
        (_, VAbsurd)  -> Absurd
        (_, VAtom)    -> Atom
-- This needs to change when universes are added
        (_, VU) -> U
        (_, VEqual t from to) ->
          Equal
          (go d (Just VU, t))
          (go d (Just t, from))
          (go d (Just t, to))
        (_, VSigma n carT cdrT) ->
         let
           varV  = VNeutral (Just carT) (NVar fresh)
           cdrV  = cdrT varV
           cdrTFin = go fresh (Just VU, cdrV)
           carTFin = go d (Just VU, carT)
         in
           Sigma n carTFin cdrTFin
        (_, VPi n domT depT) ->
         let
           varV  = VNeutral (Just domT) (NVar fresh)
           domTFin = go d (Just VU, domT)
           depTV = appClos depT varV
           depTFin = go fresh (Just VU, depTV)
         in
          Pi n domTFin depTFin
        (_, VNeutral _ neu) -> localReadNeu neu
        (tyE, vE) -> readBackError "readBackTyped" tyE vE

level2Index :: Int -> Int -> Int
level2Index depth l = depth - l - 1

readBackNeutral :: Bool -> MCtxt -> Int -> Neutral -> Expr
readBackNeutral unf mctxt depth =
  let
    localReadNeutral = readBackNeutral unf mctxt depth
    localReadNormal  = readBackNormal unf mctxt depth
    localReadTyped   = readBackTyped unf mctxt depth
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
        (\ ~(Normal ty val) acc -> App acc (localReadTyped ty val))
        hdN
        sp
--  (NVar i) -> Var (depth - i - 1)
  (NCar neu) -> Car (localReadNeutral neu)
  (NCdr neu) -> Cdr (localReadNeutral neu)
  (NIndNat n mot base step) ->
    IndNat
      (localReadNeutral n)
      (localReadNormal mot)
      (localReadNormal base)
      (localReadNormal step)
  (NReplace eq mot base) ->
    Replace
      (localReadNeutral eq)
      (localReadNormal mot)
      (localReadNormal base)
  (NIndAbsurd absurd ty) ->
    IndAbsurd
      (The Absurd (localReadNeutral absurd))
      (localReadNormal ty)


readBackError :: String -> (Maybe Value) -> Value -> Expr
readBackError funName _ _ = error $
  unlines $
    [ "Internal error (" <> funName <> "): typecheckerError"
    ]

fullyUnfold :: Bool
fullyUnfold = True

noUnfold :: Bool
noUnfold = False


data PRename = PRename
  { domL :: Int
  , codL :: Int
  , ren  :: IntMap Int
  }

extPR :: PRename -> PRename
extPR (PRename lenD lenR ren) = PRename (lenD + 1) (lenR + 1) (IntMap.insert lenR lenD ren)

invert :: forall m . (MonadError UnifyError m) => Int -> [Value] -> ElabM m PRename
invert gamma sp = do
  (dom, ren) <- go sp
  pure $ PRename dom gamma ren
  where
    go :: [Value] -> ElabM m (Int, IntMap Int)
    go [] = pure (0, mempty)
    go (t : sp) = do
      (domL, ren) <- go sp
      tV <- forceM t
      case tV of
        VVar i | IntMap.notMember i ren -> pure (domL + 1, IntMap.insert i domL ren)
        _ -> throwError VariableError


rename
  :: forall m . (MonadError UnifyError m)
  => Int -> PRename -> Value -> ElabM m Expr
rename meta pren v = do go pren v
  where
  goSp :: PRename -> Expr -> [Value] -> ElabM m Expr
  goSp pr t [] = pure t
  goSp pr t (u : sp) = App <$> goSp pren t sp <*> go pren u
    
  go :: PRename -> Value -> ElabM m Expr
  go pr t = do
    (_, mCtxt) <- get
    tV <- forceM t
    case tV of
      VMetaSp meta' sp | meta == meta' -> throwError OccursCheck
                       | otherwise     -> goSp pr (Meta meta') (fmap normalVal sp)

      VLam n clos -> Lam n <$> go (extPR pr) (appClos clos (VVar (codL pr)))
                                       -- We apply the codL variable
                                       -- as the term we are renaming will
                                       -- live under that many lambdas
                                       -- and we are using levels.
      VSigma n ty clos ->
        Sigma n
          <$> go pr ty
          <*> go (extPR pr) (appClos clos (VVar (codL pr)))
      VPi n ty clos ->
        Pi n
          <$> go pr ty
          <*> go (extPR pr) (appClos clos (VVar (codL pr)))          
          
      VPair car cdr -> Cons <$> (go pr car) <*> (go pr cdr)
      VNat -> pure Nat
      VZero -> pure Zero
      VAdd1 v -> Add1 <$> go pr v
      VEqual ty from to -> Equal <$> (go pr ty) <*> (go pr from) <*> (go pr to)
      VSame -> pure Same
      VTrivial -> pure Trivial
      VSole -> pure Sole
      VAbsurd -> pure Absurd
      VAtom -> pure Atom
      VTick chrs -> pure $ Tick chrs
      VU -> pure U
      VTop name _ _ _ -> pure (Top name)
      VNeutral _ neu -> goNeu pr neu

  goNeu :: PRename -> Neutral -> ElabM m Expr
  goNeu pr = \case
    NSpine (HTop n) sp -> goSp pr (Top n) (fmap normalVal sp)
    NSpine (HVar i) sp -> case IntMap.lookup i (ren pr) of
      Just i' -> goSp pr (Var $ level2Index (domL pr) i') (fmap normalVal sp)
      Nothing -> throwError ScopeError
      
    NCar neu' -> Car <$> goNeu pr neu'
    NCdr neu' -> Cdr <$> goNeu pr neu'
    NIndNat neu' norm1 norm2 norm3 ->
      IndNat
        <$> (goNeu pr neu')
        <*> go pr (normalVal norm1)
        <*> go pr (normalVal norm2)
        <*> go pr (normalVal norm3)
    NReplace neu' norm1 norm2 ->
      Replace
        <$> (goNeu pr neu')
        <*> go pr (normalVal norm1)
        <*> go pr (normalVal norm2)
    NIndAbsurd neu' norm ->
      IndAbsurd
        <$> (goNeu pr neu')
        <*> go pr (normalVal norm)


quoteM :: (Monad m) => Bool -> Int -> (Maybe Ty) -> Value -> ElabM m Expr
quoteM unf depth ty val =
  gets $ \ (_, mctxt) -> readBackTyped unf mctxt depth ty val

valueToString :: Value -> String
valueToString = undefined


unfoldTopVar :: TopEnv -> Name -> Expr
unfoldTopVar topEnv n =
  let
    readBack = readBackTyped fullyUnfold mempty 0 Nothing
  in
    readBack (evalTopVar topEnv n)


-- create a fresh metavariable and give back the meta expanded with all variables in scope.
lams :: Int -> Expr -> Expr
lams depth = go 0
  where
    go i t | i == depth = t
    go i t = Lam (newVar <> show i) $ go (i + 1) t

solve
  :: (MonadError UnifyError m)
  => TopEnv -> Int -> Meta -> [Value] -> Value -> ElabM m ()
solve topEnv depth meta sp rhsV = do
  pr <- invert depth sp
  renamedRHS <- rename meta pr rhsV
  solution <- evalM (topEnv, mempty) $ lams depth renamedRHS
  modify' (second $ IntMap.insert meta solution)


unify :: forall m . (MonadError UnifyError m)
  => TopEnv -> Value -> Value -> ElabM m ()
unify topEnv = go 0 where
  go :: Int -> Value -> Value -> ElabM m ()
  go depth lhs rhs = do
    metaSub <- gets snd
    case (force metaSub lhs, force metaSub rhs) of
      (VLam _ body1, VLam _ body2) ->
        let
          varV = VVar depth
          body1' = appClos body1 varV
          body2' = appClos body2 varV
        in
          go (depth + 1) body1' body2'
      (VLam _ body1, f2) ->
        let
          depth' = depth + 1
          varV = VVar depth
        in
          go (depth + 1) (body1 varV) (doApply f2 varV)
      (f1, VLam _ body2) ->
        let
          depth' = depth + 1
          varV   = VVar depth
        in
          go (depth + 1) (body2 varV) (doApply f1 varV) 
      (VSigma _ dom1T dep1T, VSigma _ dom2T dep2T) ->
        let
          depth' = depth + 1
          varV  = VVar depth
        in
          go depth dom1T dom2T >>
          go depth' (dep1T varV) (dep2T varV)
      (VPi _ dom1T dep1T, VPi _ dom2T dep2T) ->
        let
          depth' = depth + 1
          varV  = VVar depth
        in
          go depth dom1T dom2T >>
          go depth' (dep1T varV) (dep2T varV)  
      (VPair car1 cdr1, VPair car2 cdr2) ->
        go depth car1 car2 >>
        go depth cdr1 cdr2
      (VNeutral _ (NSpine hd1 sp1), VNeutral _ (NSpine hd2 sp2))
        | hd1 == hd2 -> goSp depth sp1 sp2
      (VNeutral Nothing (NSpine (HMeta m1) sp1), f2) ->
        solve topEnv depth m1 (fmap normalVal sp1) f2
      (f1, VNeutral Nothing (NSpine (HMeta m2) sp2)) ->
        solve topEnv depth m2 (fmap normalVal sp2) f1
      (VEqual ty1 from1 to1, VEqual ty2 from2 to2) ->
        go depth ty1 ty2     >>
        go depth from1 from2 >>
        go depth to1 to2
      (cstr1, cstr2) | cmpConstrs cstr1 cstr2 == True -> pure ()
      (t1, t2) -> do
        t1N <- quoteM True depth Nothing t1
        t2N <- quoteM True depth Nothing t2
        throwError $ UnifyError t1N t2N

  goSp :: Int -> [Normal] -> [Normal] -> ElabM m ()
  goSp depth sp1 sp2 = case (sp1, sp2) of
    ([], []) -> pure ()
    (u1 : sp1' , u2 : sp2') ->
      go depth (normalVal u1) (normalVal u2) >>
      goSp depth sp1' sp2'
      

freshMeta
  :: (Monad m)
  => ElabM m Expr
freshMeta = do
  (meta, _) <- get
  modify' (first (+ 1))
  pure $ Meta meta

check :: forall m . (Monad m, MonadError UnifyError m) =>
  TopEnv -> TyEnv -> RawExpr -> Ty -> ElabM m Expr
check topEnv = go 0
  where
    go :: Int -> TyEnv -> RawExpr -> Ty -> ElabM m Expr
    go depth tyEnv exprR ty = do
      tySolved <- forceM ty
      case (exprR, tySolved) of
        (LamR n body, VPi _ domT depT) -> do
          let
            varV = VVar depth
            depth' = depth + 1
            tyEnv' = extendTyEnv tyEnv domT          
          Lam n <$> go depth' tyEnv' body (appClos depT varV)
        (ConsR car cdr, VSigma _ domT depT) -> do
          let
            varV = VVar depth
            depth' = depth + 1
            tyEnv' = extendTyEnv tyEnv domT
          Cons <$> go depth  tyEnv  car domT
               <*> go depth' tyEnv' cdr (appClos depT varV)
        (SameR, VEqual mot from to) -> do
          unless (conv' mot from to)
            (throwError $ ConvError from to)
          pure Same
        (HoleR, _) ->
          freshMeta
        _ -> do
          (expr, exprTyV) <- synth topEnv tyEnv exprR
          unify topEnv exprTyV tySolved 
          pure expr


freshClos1 :: (Monad m) => TopEnv -> Int -> ElabM m (Ty, Closure)
freshClos1 topEnv depth = do
  dom <- freshMeta
  ~domV <- evalM (topEnv, []) dom
  let depth' = depth + 1
  dep <- freshMeta
  mctxt <- gets snd
  let ~depCl = \val -> eval mctxt topEnv [domV] dep
  pure (domV, depCl)

synth ::
  forall m . (Monad m, MonadError UnifyError m)
  => TopEnv -> TyEnv -> RawExpr -> ElabM m (Expr, Ty)
synth topEnv tyEnv = go 0 tyEnv 
  where
    go :: Int -> TyEnv -> RawExpr -> ElabM m (Expr, Ty)
    go depth tyEnv =
      \case
        LocR n -> case tyEnv ?! n of
          Nothing -> throwError ScopeError
          Just ty -> pure (Var n, ty)
        UnivR -> pure (U, VU)
        TickR chrs -> pure (Tick chrs, VAtom)
        AtomR -> pure (Atom, VU)
        AbsurdR -> pure (Absurd, VU)
        SoleR -> pure (Sole, VTrivial)
        UnitR  -> pure (Trivial, VU)
        ZeroR -> pure (Zero, VNat)
        Add1R n -> do
          (nExpr, ty) <- go depth tyEnv n
          unify topEnv ty VNat
          pure (Add1 nExpr, VNat)
        CarR p -> do
          (pExpr, pTy) <- go depth tyEnv p
          (domT, depT) <- freshClos1 topEnv depth
          let sig = VSigma newVar domT depT
          unify topEnv pTy sig
          pure (Car pExpr, domT)
        CdrR p -> do
          (pExpr, pTy) <- go depth tyEnv p
          (domT, depT) <- freshClos1 topEnv depth
          let sig = VSigma newVar domT depT
          unify topEnv pTy sig
          ~pVal <- evalM (topEnv, []) pExpr
          let pCarV = doCar pVal
          let finT = appClos depT 
          pure (Car pExpr, domT)
        TopR n -> case lookup n topEnv of
          Nothing -> throwError ScopeError
          Just norm ->
            let
              ~expr = normalVal norm
              ty    = normalTy  norm
            in
              case ty of
                Nothing -> throwError $ TopLevelNoType n
                Just ty -> pure (Top n, ty)
        IndNatR tgt mot base step -> do
          (tgtE, tgtTy) <- go depth tyEnv tgt
          unify topEnv tgtTy VNat
          pure undefined          
