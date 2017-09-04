{-# LANGUAGE RankNTypes #-}
module GalleyCode where 

import Control.Monad (sequence)

-- import Text.PrettyPrint

import Prelude

import Debug.Trace 

import Text.PrettyPrint.Boxes
    
testFoo :: (Show a) => a -> a
testFoo x = trace ("\nTesting Value: " ++ show x ++ "\n") x
fooBar :: (Show a) => String -> a -> a
fooBar str x = trace ("\n" ++ str ++ "  "++ show x ++ "\n") x

splitList :: [a] -> [[a]]
splitList [] = []
splitList (x:xs) = [x]:splitList xs

data EvalResult a
  = Disappearing
  | Suspended { obj  :: a }
  | NoSpace   { obj  :: a }
  | Sending   { gall :: [Galley a]
              , obj  :: a }
  | Yielding  { comp :: Component
              , obj  :: a }

type Constraint = Maybe Int

type Component = [Box]
convertBox :: [String] -> [Box]
convertBox = map text
-- Tag , Direction , VObject
-- type Galley = (String, Direction, VObject)
data Galley a = Galley 
            { tName :: String 
            , direction :: Direction
            , galleyObject :: a
            } deriving (Show)

data Direction
  = Preceding
  | Following
  deriving (Show)

type MeasuredDimension = Int 

data RcvResult a = RcvResult { resultSuccess :: Bool
, galleyYield :: [Galley a]
, resultValue :: a
}

type OCState a = (Bool, a, a)

type STfun s x = s -> (s, x)

type SToc a = STfun (OCState a) [Galley a]

class Constrainer c where
  cDim :: c -> Int

(&-) :: Constrainer c => Constraint -> c -> Constraint
Nothing &- c = Nothing
(Just h) &- c
  | h' < 0 = Just 0
  | otherwise = Just h'
  where
    h' = h - cDim c

(&?) :: Constrainer c => Constraint -> c -> Bool
Nothing &? c = True
(Just h) &? c = h >= cDim c

instance Constrainer Int where
  cDim n = n

instance Constrainer c => Constrainer (Maybe c) where
  cDim Nothing = 0
  cDim (Just o) = cDim o

class IsChar c where
  ischar :: c

instance IsChar Char where
  ischar = '?'

class IsString s where
  isstring :: s

instance IsChar a => IsString [a] where
  isstring = [ischar]

instance IsString a => Constrainer [a] where
  cDim c = length c

instance IsString Box where
  isstring = text "?" 
instance IsChar Box where
  ischar = text "?"
instance Constrainer Box where
  cDim n = rows n

infixr 6 #
class Constrainer a => GalleyComponent a where 
  evaluateGC       :: a -> ShouldForce -> Constraint -> EvalResult a
  receiveGC        :: a -> ShouldForce -> Constraint -> Galley a -> RcvResult a
  openTargetsGC    :: a -> [String]
  delayedTargetsGC :: a -> [String]
  dimGC            :: a -> Int
  nul :: a
  force :: a -> [Component]
  prepareComp :: a -> ([Box] -> Box)
  singleton :: Component -> a
  prefix :: Component -> a -> a
  galley :: Galley a -> a
  suffix :: Component -> a -> a
  (#) :: a -> a -> a
  high :: Int -> a -> a
  prefixConc :: Component -> a -> a
  attach :: String -> a -> a
  target :: String -> a
  recurse :: (a -> a) -> a
  delay :: a -> a
  vExpand :: a -> a
  recurseF :: ((b -> a) -> (b -> a)) -> (b -> a)

  
data HObject = HObject
  { heval           :: ShouldForce -> Constraint -> EvalResult HObject
  , hreceive        :: ShouldForce -> Constraint -> Galley HObject -> RcvResult HObject
  , hopenTargets    :: [String]
  , hdelayedTargets :: [String]
  , hhigh         :: Int
  } -- deriving Show
instance Show HObject where
  show obj =
    "Open Targets: " ++
    (show $ hopenTargets obj) ++
    "Delayed Targets: " ++
    (show $ hdelayedTargets obj) ++ 
    "Object Width: " ++ (show $ hhigh obj)
instance Constrainer HObject where
  cDim = hhigh
instance GalleyComponent HObject where
  evaluateGC       = heval          
  receiveGC        = hreceive       
  openTargetsGC    = hopenTargets   
  delayedTargetsGC = hdelayedTargets
  dimGC            = cDim  
  nul = HObject
      { heval = (\forcing co -> Disappearing)
      , hreceive = (\forcing co g -> rcverror g "nul")
      , hopenTargets = []
      , hdelayedTargets = []
      , hhigh = 0
      }
  force o =
    case heval o True Nothing of
      Disappearing -> []
      Yielding c o' -> c : force o'
      Sending gs o' -> force o'
  singleton c = o
    where
      o =
        HObject
        { heval =
            (\forcing co ->
                if co &? c
                  then Yielding c nul
                  else NoSpace o)
        , hreceive = (\forcing co g -> rcverror g "singleton")
        , hopenTargets = []
        , hdelayedTargets = []
        , hhigh = length c
        }
  prefix c o = o'
    where
      o' =
        HObject
        { heval =
            (\forcing co ->
                if co &? c
                  then Yielding c o
                  else NoSpace o')
        , hreceive =
            (\forcing co g -> updateRcvResult (prefix c) $ hreceive o forcing (co &- c) g)
        , hopenTargets = hopenTargets o
        , hdelayedTargets = hdelayedTargets o
        , hhigh = length c + hhigh o
        }
  galley g =
    HObject
    { heval = (\forcing co -> Sending [g] nul)
    , hreceive = (\forcing co g' -> rcverror g' "galley")
    , hopenTargets = []
    , hdelayedTargets = []
    , hhigh = 0
    }
  suffix c o = o'
    where
      o' =
        HObject
        { heval =
            (\forcing co ->
                case heval o forcing (co &- c) of
                  Disappearing -> heval (singleton c) forcing co
                  r -> r {obj = suffix c (obj r)})
        , hreceive =
            (\forcing co g -> updateRcvResult (suffix c) $ hreceive o forcing (co &- c) g)
        , hopenTargets = hopenTargets o
        , hdelayedTargets = hdelayedTargets o
        , hhigh = length c + hhigh o
        }
  o1 # o2 = o
    where
      o =
        HObject
        { heval = ocEval o1 o2
        , hreceive =
            (\forcing co g@(Galley name d o') ->
                let send1 =
                      let RcvResult r gs o1' = hreceive o1 forcing (co &- o2) g
                      in ocMkResult $ ocGalleysFrom1 forcing co gs (r, o1', o2)
                    send2 =
                      let RcvResult r gs o2' = hreceive o2 True (co &- o1) g
                      in ocMkResult $ ocGalleysFrom2 forcing co gs (r, o1, o2')
                    sendO1 x =
                      if name `elem` hopenTargets o1
                        then send1
                        else x
                    sendO2 x =
                      if name `elem` hopenTargets o2
                        then send2
                        else x
                    sendD1 x =
                      if name `elem` hdelayedTargets o1
                        then send1
                        else x
                    sendD2 x =
                      if name `elem` hdelayedTargets o2
                        then send2
                        else x
                in case d of
                    Following ->
                      sendO1 $ sendO2 $ sendD1 $ sendD2 $ rcverror g "(#)"
                    Preceding ->
                      sendO2 $ sendO1 $ sendD2 $ sendD1 $ rcverror g "(#)")
        , hopenTargets = hopenTargets o1 ++ hopenTargets o2
        , hdelayedTargets = hdelayedTargets o1 ++ hdelayedTargets o2
        , hhigh = hhigh o1 + hhigh o2
        }
  high h o = o'
    where
      eval' forcing =
        case heval o forcing (Just h) of
          NoSpace o1 -> Yielding (fill h (convertBox ["@High: HObject too large"])) nul
          Disappearing -> Yielding (strut h) nul
          Suspended o1 -> Suspended (high h o1)
          Sending gs o1 -> Sending gs (high h o1)
          Yielding c o1 ->
            let h' = h - length c
            in if h' < 0
                  then error "@High: yielded component too hhigh!"
                  else case heval (high h' o1) forcing Nothing of
                        Yielding c' o2 -> Yielding (c ++ c') o2
                        Sending gs o2 -> Sending gs (prefixConc c o2)
                        Suspended o2 -> Suspended (prefixConc c o2)
                        NoSpace o2 -> error "@High: NoSpace in recursive call!"
                        Disappearing -> Yielding (fill h c) nul
      o' =
        HObject
        { heval =
            (\forcing co ->
                case co of
                  Nothing -> eval' forcing
                  Just h' ->
                    if h' < h
                      then NoSpace o'
                      else eval' forcing)
        , hreceive =
            (\forcing co g -> updateRcvResult (high h) $ hreceive o forcing (Just h) g)
        , hopenTargets = hopenTargets o
        , hdelayedTargets = hdelayedTargets o
        , hhigh = h
        }
  prefixConc c o = o'
    where
      o' =
        HObject
        { heval =
            (\forcing co ->
                case heval o forcing (co &- c) of
                  Disappearing -> Yielding c nul
                  Yielding c' o2 -> Yielding (c ++ c') o2
                  r -> r {obj = prefixConc c (obj r)})
        , hreceive =
            (\forcing co g ->
                if co &? c
                  then updateRcvResult (prefixConc c) $ hreceive o forcing (co &- c) g
                  else RcvResult False [forward g] o')
        , hopenTargets = hopenTargets o
        , hdelayedTargets = hdelayedTargets o
        , hhigh = length c + hhigh o
        }
  attach name = attach'
    where
      attach' o = o'
        where
          o' =
            HObject
            { heval =
                (\forcing co ->
                    case heval o forcing Nothing of
                      Disappearing -> Disappearing
                      NoSpace o1 -> error "attach: NoSpace without constraints!"
                      Suspended o1 ->
                        if isConstraintMet co
                          then Sending [Galley name Following (attach' o1)] nul
                          else Suspended (attach' o1)
                      Sending gs o1 -> Sending gs (attach' o1)
                      Yielding c o1 ->
                        if co &? c
                          then Yielding c (attach' o1)
                          else Sending
                                [Galley name Following $ attach' (prefix c o1) ]
                                nul)
            , hreceive =
                (\forcing co g -> updateRcvResult attach' $ hreceive o forcing co g)
            , hopenTargets = hopenTargets o
            , hdelayedTargets = hdelayedTargets o
            , hhigh = 0
            }
  target name = o
    where
      o =
        HObject
        { heval =
            (\forcing co ->
                if forcing
                  then Disappearing
                  else case co of
                        Just 0 -> Disappearing
                        _ -> Suspended o)
        , hreceive =
            (\forcing co g@(Galley name' d' o') ->
                case co of
                  _ ->
                    if name /= name'
                      then rcverror g "target"
                      else if not forcing
                            then RcvResult True [] (attach name o' # o)
                            else case heval o' False Nothing of
                                    Disappearing -> RcvResult True [] o
                                    Suspended o'' ->
                                      RcvResult True [] (attach name o'' # o)
                                    NoSpace o'' ->
                                      error "target: NoSpace without constraint!"
                                    Sending gs1 o'' ->
                                      RcvResult True gs1 (attach name o'' # o)
                                    Yielding c o'' ->
                                      if co &? c
                                        then let g' = Galley name' Following o''
                                                 RcvResult rcv gs1 o1 = 
                                                   hreceive
                                                   (prefix c o)
                                                   forcing
                                                   co
                                                   g'
                                            in RcvResult True gs1 o1
                                        else RcvResult False
                                                        [Galley name Following $ prefix c o'']
                                                        nul)
        , hopenTargets = [name]
        , hdelayedTargets = []
        , hhigh = 0
        }
  recurse ff = o
    where
      ffo = ff o
      ff0 = ff nul -- List Of strings | hopenTargets o ++ hdelayedTargets o
      targs = targets ff0
      o =
        HObject
        { heval =
            (\forcing co ->
                if forcing || isConstraintMet co || not (co &? ffo)
                  then Disappearing
                  else Suspended o)
        , hreceive =
            (\forcing co g@(Galley name d o') ->
                case co of
                  Just 0 -> RcvResult False [forward g] nul
                  _ ->
                    if name `elem` targs
                      then case hreceive ff0 forcing co g of
                            RcvResult False gs o1 -> RcvResult False [forward g] nul
                            r -> hreceive ffo forcing co g
                      else rcverror g "recurse")
        , hopenTargets = []
        , hdelayedTargets = targs
        , hhigh = 0
        }
  delay o = o'
    where
      o' =
        HObject
        { heval =
            (\forcing co ->
                if forcing || isConstraintMet co || not (co &? o)
                  then Disappearing
                  else Suspended o')
        , hreceive =
            (\forcing co g@(Galley name d o') ->
                case co of
                  Just 0 -> RcvResult False [forward g] nul
                  _ ->
                    if name `elem` targs
                      then case hreceive o forcing co g of
                            RcvResult False gs o1 -> RcvResult False [forward g] nul
                            r -> r
                      else rcverror g "delay")
        , hopenTargets = []
        , hdelayedTargets = targs
        , hhigh = 0
        }
      targs = targets o
  vExpand o = o'
    where
      o' =
        HObject
        { heval =
            (\forcing co ->
                case co of
                  Nothing -> heval o forcing co
                  Just 0 -> heval o forcing co
                  Just h ->
                    case heval o forcing co of
                      Disappearing -> Yielding (strut h) nul
                      NoSpace o1 -> NoSpace o1
                      Sending gs o1 -> Sending gs (vExpand o1)
                      Suspended o1 -> Suspended (vExpand o1)
                      Yielding c o1 ->
                        Yielding
                          c
                          (if length c < h
                            then vExpand o1
                            else o1))
        , hreceive = (\frc co g -> updateRcvResult vExpand (hreceive o frc co g))
        , hopenTargets = hopenTargets o
        , hdelayedTargets = hdelayedTargets o
        , hhigh = hhigh o
        }
  recurseF ff = f
    where
      f' = ff f
      f a = o -- fooBar "o is called"  $
        where
          ffo = f' a
          ff0 = ff (const nul) a
          targs = targets ff0
          o =
            HObject -- { as before }
            { heval =
                (\forcing co ->
                    if forcing || isConstraintMet co || not (co &? ffo)
                      then Disappearing
                      else Suspended o)
            , hreceive =
                (\forcing co g@(Galley name d o') ->
                    case co of
                      Just 0 -> RcvResult False [forward g] nul
                      _ ->
                        if name `elem` targs
                          then case hreceive ff0 forcing co g of
                                    RcvResult False gs o1 -> RcvResult False [forward g] nul
                                    r -> hreceive ffo forcing co g
                          else rcverror g "recurseF")
            , hopenTargets = []
            , hdelayedTargets = targs
            , hhigh = 0
            }
  prepareComp _ = hcat left
type ShouldForce = Bool 
data VObject = VObject
  { eval           :: ShouldForce -> Constraint -> EvalResult VObject
  , receive        :: ShouldForce -> Constraint -> Galley VObject -> RcvResult VObject
  , openTargets    :: [String]
  , delayedTargets :: [String]
  , height         :: Int
  } -- deriving Show
instance Show VObject where
  show obj =
    "Open Targets: " ++
    (show $ openTargets obj) ++
    "Delayed Targets: " ++
    (show $ delayedTargets obj) ++ 
    "Object Height: " ++ (show $ height obj)
instance Constrainer VObject where
  cDim = height
instance GalleyComponent VObject where
  evaluateGC       = eval          
  receiveGC        = receive       
  openTargetsGC    = openTargets   
  delayedTargetsGC = delayedTargets
  dimGC            = cDim  
  nul = VObject
      { eval = (\forcing co -> Disappearing)
      , receive = (\forcing co g -> rcverror g "nul")
      , openTargets = []
      , delayedTargets = []
      , height = 0
      }
  force o =
    case eval o True Nothing of
      Disappearing -> []
      Yielding c o' -> c : force o'
      Sending gs o' -> force o'
  singleton c = o
    where
      o =
        VObject
        { eval =
            (\forcing co ->
                if co &? c
                  then Yielding c nul
                  else NoSpace o)
        , receive = (\forcing co g -> rcverror g "singleton")
        , openTargets = []
        , delayedTargets = []
        , height = length c
        }
  prefix c o = o'
    where
      o' =
        VObject
        { eval =
            (\forcing co ->
                if co &? c
                  then Yielding c o
                  else NoSpace o')
        , receive =
            (\forcing co g -> updateRcvResult (prefix c) $ receive o forcing (co &- c) g)
        , openTargets = openTargets o
        , delayedTargets = delayedTargets o
        , height = length c + height o
        }
  galley g =
    VObject
    { eval = (\forcing co -> Sending [g] nul)
    , receive = (\forcing co g' -> rcverror g' "galley")
    , openTargets = []
    , delayedTargets = []
    , height = 0
    }
  suffix c o = o'
    where
      o' =
        VObject
        { eval =
            (\forcing co ->
                case eval o forcing (co &- c) of
                  Disappearing -> eval (singleton c) forcing co
                  r -> r {obj = suffix c (obj r)})
        , receive =
            (\forcing co g -> updateRcvResult (suffix c) $ receive o forcing (co &- c) g)
        , openTargets = openTargets o
        , delayedTargets = delayedTargets o
        , height = length c + height o
        }
  o1 # o2 = o
    where
      o =
        VObject
        { eval = ocEval o1 o2
        , receive =
            (\forcing co g@(Galley name d o') ->
                let send1 =
                      let RcvResult r gs o1' = receive o1 forcing (co &- o2) g
                      in ocMkResult $ ocGalleysFrom1 forcing co gs (r, o1', o2)
                    send2 =
                      let RcvResult r gs o2' = receive o2 True (co &- o1) g
                      in ocMkResult $ ocGalleysFrom2 forcing co gs (r, o1, o2')
                    sendO1 x =
                      if name `elem` openTargets o1
                        then send1
                        else x
                    sendO2 x =
                      if name `elem` openTargets o2
                        then send2
                        else x
                    sendD1 x =
                      if name `elem` delayedTargets o1
                        then send1
                        else x
                    sendD2 x =
                      if name `elem` delayedTargets o2
                        then send2
                        else x
                in case d of
                    Following ->
                      sendO1 $ sendO2 $ sendD1 $ sendD2 $ rcverror g "(#)"
                    Preceding ->
                      sendO2 $ sendO1 $ sendD2 $ sendD1 $ rcverror g "(#)")
        , openTargets = openTargets o1 ++ openTargets o2
        , delayedTargets = delayedTargets o1 ++ delayedTargets o2
        , height = height o1 + height o2
        }
  high h o = o'
    where
      eval' forcing =
        case eval o forcing (Just h) of
          NoSpace o1 -> Yielding (fill h (convertBox(["@High: VObject too large"]))) nul
          Disappearing -> Yielding (strut h) nul
          Suspended o1 -> Suspended (high h o1)
          Sending gs o1 -> Sending gs (high h o1)
          Yielding c o1 ->
            let h' = h - length c
            in if h' < 0
                  then error "@High: yielded component too high!"
                  else case eval (high h' o1) forcing Nothing of
                        Yielding c' o2 -> Yielding (c ++ c') o2
                        Sending gs o2 -> Sending gs (prefixConc c o2)
                        Suspended o2 -> Suspended (prefixConc c o2)
                        NoSpace o2 -> error "@High: NoSpace in recursive call!"
                        Disappearing -> Yielding (fill h c) nul
      o' =
        VObject
        { eval =
            (\forcing co ->
                case co of
                  Nothing -> eval' forcing
                  Just h' ->
                    if h' < h
                      then NoSpace o'
                      else eval' forcing)
        , receive =
            (\forcing co g -> updateRcvResult (high h) $ receive o forcing (Just h) g)
        , openTargets = openTargets o
        , delayedTargets = delayedTargets o
        , height = h
        }
  prefixConc c o = o'
    where
      o' =
        VObject
        { eval =
            (\forcing co ->
                case eval o forcing (co &- c) of
                  Disappearing -> Yielding c nul
                  Yielding c' o2 -> Yielding (c ++ c') o2
                  r -> r {obj = prefixConc c (obj r)})
        , receive =
            (\forcing co g ->
                if co &? c
                  then updateRcvResult (prefixConc c) $ receive o forcing (co &- c) g
                  else RcvResult False [forward g] o')
        , openTargets = openTargets o
        , delayedTargets = delayedTargets o
        , height = length c + height o
        }
  attach name = attach'
    where
      attach' o = o'
        where
          o' =
            VObject
            { eval =
                (\forcing co ->
                    case eval o forcing Nothing of
                      Disappearing -> Disappearing
                      NoSpace o1 -> error "attach: NoSpace without constraints!"
                      Suspended o1 ->
                        if isConstraintMet co
                          then Sending [Galley name Following (attach' o1)] nul
                          else Suspended (attach' o1)
                      Sending gs o1 -> Sending gs (attach' o1)
                      Yielding c o1 ->
                        if co &? c
                          then Yielding c (attach' o1)
                          else Sending
                                [Galley name Following $ attach' (prefix c o1) ]
                                nul)
            , receive =
                (\forcing co g -> updateRcvResult attach' $ receive o forcing co g)
            , openTargets = openTargets o
            , delayedTargets = delayedTargets o
            , height = 0
            }
  target name = o
    where
      o =
        VObject
        { eval =
            (\forcing co ->
                if forcing
                  then Disappearing
                  else case co of
                        Just 0 -> Disappearing
                        _ -> Suspended o)
        , receive =
            (\forcing co g@(Galley name' d' o') ->
                case co of
                  _ ->
                    if name /= name'
                      then rcverror g "target"
                      else if not forcing
                            then RcvResult True [] (attach name o' # o)
                            else case eval o' False Nothing of
                                    Disappearing -> RcvResult True [] o
                                    Suspended o'' ->
                                      RcvResult True [] (attach name o'' # o)
                                    NoSpace o'' ->
                                      error "target: NoSpace without constraint!"
                                    Sending gs1 o'' ->
                                      RcvResult True gs1 (attach name o'' # o)
                                    Yielding c o'' ->
                                      if co &? c
                                        then let g' = Galley name' Following o''
                                                 RcvResult rcv gs1 o1 = 
                                                   receive
                                                   (prefix c o)
                                                   forcing
                                                   co
                                                   g'
                                            in RcvResult True gs1 o1
                                        else RcvResult False
                                                        [Galley name Following $ prefix c o'']
                                                        nul)
        , openTargets = [name]
        , delayedTargets = []
        , height = 0
        }
  recurse ff = o
    where
      ffo = ff o
      ff0 = ff nul -- List Of strings | openTargets o ++ delayedTargets o
      targs = targets ff0
      o =
        VObject
        { eval =
            (\forcing co ->
                if forcing || isConstraintMet co || not (co &? ffo)
                  then Disappearing
                  else Suspended o)
        , receive =
            (\forcing co g@(Galley name d o') ->
                case co of
                  Just 0 -> RcvResult False [forward g] nul
                  _ ->
                    if name `elem` targs
                      then case receive ff0 forcing co g of
                            RcvResult False gs o1 -> RcvResult False [forward g] nul
                            r -> receive ffo forcing co g
                      else rcverror g "recurse")
        , openTargets = []
        , delayedTargets = targs
        , height = 0
        }
  delay o = o'
    where
      o' =
        VObject
        { eval =
            (\forcing co ->
                if forcing || isConstraintMet co || not (co &? o)
                  then Disappearing
                  else Suspended o')
        , receive =
            (\forcing co g@(Galley name d o') ->
                case co of
                  Just 0 -> RcvResult False [forward g] nul
                  _ ->
                    if name `elem` targs
                      then case receive o forcing co g of
                            RcvResult False gs o1 -> RcvResult False [forward g] nul
                            r -> r
                      else rcverror g "delay")
        , openTargets = []
        , delayedTargets = targs
        , height = 0
        }
      targs = targets o
  vExpand o = o'
    where
      o' =
        VObject
        { eval =
            (\forcing co ->
                case co of
                  Nothing -> eval o forcing co
                  Just 0 -> eval o forcing co
                  Just h ->
                    case eval o forcing co of
                      Disappearing -> Yielding (strut h) nul
                      NoSpace o1 -> NoSpace o1
                      Sending gs o1 -> Sending gs (vExpand o1)
                      Suspended o1 -> Suspended (vExpand o1)
                      Yielding c o1 ->
                        Yielding
                          c
                          (if length c < h
                            then vExpand o1
                            else o1))
        , receive = (\frc co g -> updateRcvResult vExpand (receive o frc co g))
        , openTargets = openTargets o
        , delayedTargets = delayedTargets o
        , height = height o
        }
  recurseF ff = f
    where
      f' = ff f
      f a = o -- fooBar "o is called"  $
        where
          ffo = f' a
          ff0 = ff (const nul) a
          targs = targets ff0
          o =
            VObject -- { as before }
            { eval =
                (\forcing co ->
                    if forcing || isConstraintMet co || not (co &? ffo)
                      then Disappearing
                      else Suspended o)
            , receive =
                (\forcing co g@(Galley name d o') ->
                    case co of
                      Just 0 -> RcvResult False [forward g] nul
                      _ ->
                        if name `elem` targs
                          then case receive ff0 forcing co g of
                                    RcvResult False gs o1 -> RcvResult False [forward g] nul
                                    r -> receive ffo forcing co g
                          else rcverror g "recurseF")
            , openTargets = []
            , delayedTargets = targs
            , height = 0
            }
  prepareComp _ = vcat left

ocGalleysFrom1, ocGalleysFrom2 :: GalleyComponent a => Bool -> Constraint -> [Galley a] -> SToc a
ocGalleysFrom1 forcing co = stfold (ocGalleyFrom1 forcing co)

ocGalleysFrom2 forcing co = stfold (ocGalleyFrom2 forcing co)

ocGalleyFrom1, ocGalleyFrom2 :: GalleyComponent a => Bool -> Constraint -> Galley a -> SToc a
ocGalleyFrom1 forcing co g@(Galley name Preceding _) s = (s, [g])
ocGalleyFrom1 forcing co g@(Galley name Following _) s@(rcv, o1, o2) =
  if name `notElem` targets o2
    then (s, [g])
    else let RcvResult rcv' gs2 o2' = receiveGC o2 True (co &- o1) g
          in ocGalleysFrom2 forcing co gs2 (rcv || rcv', o1, o2')

ocGalleyFrom2 forcing co g@(Galley name Following _) s = (s, [g])
ocGalleyFrom2 forcing co g@(Galley name Preceding _) s@(rcv, o1, o2) =
  if name `notElem` targets o1
    then (s, [g])
    else let RcvResult rcv' gs1 o1' = receiveGC o1 forcing (co &- o2) g
          in ocGalleysFrom1 forcing co gs1 (rcv || rcv', o1', o2)

stfold :: (a -> STfun b [c]) -> [a] -> STfun b [c]
stfold f [] s = (s, [])
stfold f (g:gs) s =
  let (s', gs') = f g s
      (s'', gs'') = stfold f gs s'
  in (s'', gs' ++ gs'')


ocEval :: GalleyComponent a => a -> a -> Bool -> Constraint -> EvalResult a
ocEval o1 o2 forcing co =
  case evaluateGC o1 False (co &- o2) of
    Disappearing -> evaluateGC o2 forcing co
    NoSpace o1' -> NoSpace (o1' # o2)
    Yielding c o1' -> Yielding c (o1' # o2)
    Sending gs o1' ->
      case ocMkResult $ ocGalleysFrom1 False co gs (False, o1', o2) of
        RcvResult rcv [] o' -> evaluateGC o' forcing co
        RcvResult rcv gs o' -> Sending gs o'
    Suspended o1' ->
      case evaluateGC o2 forcing (co &- o1') of
        Disappearing ->
          if forcing
            then evaluateGC o1' forcing co
            else Suspended o1'
        Suspended o2' -> Suspended (o1' # o2')
        NoSpace o2' ->
          if forcing
            then NoSpace o2'
            else Suspended (o1' # o2')
        Yielding c o2' -> evaluateGC (suffix c o1' # o2') forcing co
        Sending gs o2' ->
          case ocMkResult $ ocGalleysFrom2 False co gs (False, o1', o2') of
            RcvResult True [] o' -> evaluateGC o' forcing co
            RcvResult False [] o' -> error ("empty Sending???")
            RcvResult _ gs o' -> Sending gs o'

strut :: Int -> Component
strut h = replicate h nullBox
fill :: Int -> Component -> Component
fill h c = take h (c ++ repeat nullBox)

forward :: GalleyComponent a => Galley a -> Galley a
forward (Galley name d o) = Galley name Following o

ocMkResult :: GalleyComponent a => (OCState a, [Galley a]) -> RcvResult a
ocMkResult ((rcv, o1, o2), gs) = RcvResult rcv gs (o1 # o2)

updateRcvResult :: (c -> c) -> RcvResult c -> RcvResult c
updateRcvResult f (RcvResult a b c) = RcvResult a b $ f c

targets :: GalleyComponent a => a -> [String]
targets gc = openTargetsGC gc ++ delayedTargetsGC gc

isConstraintMet :: Constraint -> Bool
isConstraintMet Nothing = False
isConstraintMet (Just 0) = True
isConstraintMet _ = False

-- displayObject :: forall a. GalleyComponent a => Int -> Int -> a -> IO ()
-- displayObject n wid o = putStr $ unlines $ frame n wid $ force o

-- frame :: Int -> Int -> [Component] -> Component
-- frame n wid [] = []
-- frame n wid cs = overline (f cs1) ++ frame n wid cs2
--   where
--     (cs1, cs2) = splitAt n cs
--     l2 s = l1 s ++ "|"
--     l1 s = '|' : take wid (s ++ repeat ' ')
--     b2 = [replicate (wid + 2) '-']
--     b1 = [replicate (wid + 1) '-']
--     p1 c = map l1 c ++ b1
--     p2 c = map l2 c ++ b2
--     f [] = []
--     f [c] = p2 c
--     f (c:cs) = zipWith (++) (p1 c) (f cs)
--     overline l@(s:ss) = replicate (length s) '-' : l

-- printObject :: VObject -> IO ()
-- printObject = putStr . string_of_Object True
-- printObject' :: VObject -> IO ()
-- printObject' = putStr . string_of_Object False

-- string_of_Object :: GalleyComponent a => Bool -> a -> String
-- string_of_Object forcing = f 10 []
--   where
--     f 0 gs o = "<<<Terminating.>>>\n"
--     f n gs o =
--       let printstray gs =
--             unlines
--               (text "====================" :
--                 map string_of_stray_galley gs ++ (convertBox(["####################"])))
--       in case evaluateGC o forcing Nothing of
--             Disappearing -> "<<<Disappearing>>>\n" ++ printstray gs
--             Suspended o' ->
--               "<<<Suspended!!!>>>\n" ++
--               printstray gs ++
--               case gs of
--                 [] -> f (n - 1) [] o'
--                 (g@(Galley name d og):gs1) ->
--                   if name `elem` targets o'
--                     then case receiveGC o' False Nothing g of
--                           RcvResult False gs2 o2 -> "<<<NoSpaceR>>>\n" ++ f (n - 1) (gs1 ++ gs2) o2
--                           RcvResult True gs2 o2 -> "<<<Received " ++ name ++ ">>>\n" ++ f n (gs1 ++ gs2) o2
--                     else f n gs1 o'
--             Sending gs' o' ->
--               "<<<Sending!!!>>>\n" ++
--               printstray gs' ++
--               case gs ++ gs' of
--                 [] -> f (n - 1) [] o'
--                 (g@(Galley name d og):gs1) ->
--                   if name `elem` targets o'
--                     then case receiveGC o' False Nothing g of
--                               RcvResult False gs2 o2 -> "<<<NoSpaceR>>>\n" ++ f (n - 1) (gs1 ++ gs2) o2
--                               RcvResult True  gs2 o2 -> "<<<Received " ++ name ++ ">>>\n" ++ f n (gs1 ++ gs2) o2
--                     else f n gs1 o'
--             NoSpace o' -> "<<<NoSpace --- continuing>>>\n" ++ f n gs o'
--             Yielding c o' -> string_of_Component c ++ f n gs o'

-- string_of_stray_galley :: GalleyComponent a => Galley a -> String
-- string_of_stray_galley (Galley name d o) =
--   "No target for galley `" ++
--   name ++
--   "&&" ++
--   show d ++
--   "; h=" ++
--   show (dimGC o) ++
--   "\n" ++
--   string_of_Object True o ++
--   "~~~~~~~~~~ end of galley `" ++ name ++ "&&" ++ show d ++ "\n"

-- string_of_Component :: Component -> String
-- string_of_Component c = unlines (map ('|' :) c ++ (convertBox(["--------------------"])))





pageList = recurse (page #)

page = high 12 (target "TextPlace" # footSect)

footSect = delay $ prefix (convertBox(["", "-----"])) footList

footList = recurse (target "FootPlace" #)

txt t = galley $ Galley "TextPlace" Preceding t

footNote f = galley $ Galley "FootPlace" Following f

npage :: Int -> VObject
npage = npage' 14

npage' :: Int -> Int -> VObject
npage' bounds n =
  high bounds $
  prefix
    (convertBox(["          - " ++ show n ++ "-", ""]))
    (vExpand (target "TextPlace") # footSect)

npageList :: VObject
npageList = npageList' 14 
npageList':: Int -> VObject
npageList' bounds =
  let f mkpl n = npage' bounds n # mkpl (n + 1)
  in recurseF f 1 -- testFoo $ 
  
nextLine' :: GalleyComponent a => Bool -> Int -> Int -> a
nextLine' showLine bounds n =
  high bounds $
  prefix
    (if showLine then (convertBox [show n ++ ":", ""]) else [])
    (vExpand (target "TextPlace"))
nextLine :: GalleyComponent a => Int -> Int -> a
nextLine = nextLine' False

nLinesList :: GalleyComponent a => Int -> a
nLinesList = nLinesList' False
nLinesList' :: GalleyComponent a => Bool -> Int -> a
nLinesList' showNum bounds =
  let f mkpl n = nextLine' showNum bounds n # mkpl (n + 1)
  in recurseF f 1 -- testFoo $ 
  
rcverror g s = error ("Cannot receive: " ++ s ++ "\n" ++ show g)


-- | Pretty Stuff
encloseSymbols :: Box -> Box -> Box -> Box 
encloseSymbols rowSym colSym = addColBarSym colSym . addRowBarSym rowSym

encloseSymbols' :: String -> String -> Box -> Box 
encloseSymbols' rowSym colSym = encloseSymbols (text rowSym) (text colSym)

encloseBoxQuick :: String -> Box -> Box
encloseBoxQuick s = encloseSymbols' s s 

encloseBoxDef :: Box -> Box
encloseBoxDef = encloseSymbols' "|" "-"

addRowBarSym :: Box -> Box -> Box
addRowBarSym sym input = hcat top [row,input,row]
  where
    ri = rows input
    row = mkRowSym sym ri
addColBarSym :: Box -> Box -> Box
addColBarSym sym input = vcat left [col,input,col] 
  where
    ci = cols input
    col = mkColSym sym ci 

mkColSym :: Box -> Int -> Box
mkColSym b l = hcat top $ replicate l b
mkRowSym :: Box -> Int -> Box
mkRowSym b l = vcat top $ replicate l b


bodycs = bodycsH

bodycsV = [
    ["  In the world of music " ,"England is supposed to be"]
  , [" a mere province. If she " ,"produces an indi fferent " ]
  , [ "composer or performer, "]
  , ["that is regarded "]
  , ["elsewhere as perfectly "]
  , ["normal and natural; but "]
  , ["if foreign students of "]
  , ["musical history have to "]
  , ["acknowledge a British "]
  , ["musical genius, he is "]
  , ["considered a freak. Such "
  , "a freak is Henry Purcell."
  , " Yet if we make a choice "
  , "of fiftee n of the world\8217s"
  , " musical classics, as "
  , "here, we find that we "
  , "cannot omit this English "
  , "m aster."] ]
bodycsH = map (map text)
        $ splitList.splitList 
        $ concat.concat 
        $ bodycsV

main = do
  putStrLn ""
  let res = forceV vObj
  putStr $ render 
         $ hcat left 
         $ map encloseBoxDef
         $ prepareComp vObj <$> res
  where 
    body :: GalleyComponent a => [Component] -> a
    body = foldr prefix nul 
    bodyWithLines :: HObject
    bodyWithLines = nLinesList' True 14 # txt (body bodycsH)
    forceH :: HObject -> [Component]
    forceH = force --[hcat left <$> force x]
    h2v :: HObject -> VObject
    h2v hObj = body . splitList $ prepareComp bodyWithLines <$> (forceH hObj)
    vObj :: VObject
    vObj = vPages $ h2v bodyWithLines
    forceV :: VObject -> [Component]
    forceV = force
    vPages v = npageList' 13 # txt (heading 1 # v)










blom n =
  singleton
    (convertBox ["(" ++ show n ++ ") Blom, Eric. Some", "Great Composers.", "Oxford, 1944."])

heading n = prefix (convertBox ["PURCELL(" ++ show n ++ ")"]) $ footNote (blom n)

-- purcell = heading 1 # body



-- body2 :: HObject
-- body2 = foldr prefix nul (bodycs ++ bodycs)

-- example = pageList # txt purcell

-- nexample = npageList # txt purcell

-- h2a :: VObject
-- h2a = heading 1 # heading 2

-- conc :: GalleyComponent a => a -> a -> a
-- conc o1 o2 = o1 # o2

-- h3a :: VObject
-- h3a = conc (heading 1) (conc (heading 2) (heading 3))

-- h3'npl = conc npageList (txt h3a)

-- bp = conc npageList (txt (conc (conc (blom 1) body) purcell))

-- bh = conc npageList (txt (conc (blom 1) (conc body (heading 2))))

-- pg' n = high n $ conc (vExpand (target "TextPlace")) footsect

-- pg n = high n $ conc (target "TextPlace") footsect

-- pgList' n = recurse (conc (pg' n))

-- pgList n = recurse (conc (pg n))

-- doc n o = conc (pgList n) (txt o)

-- doc' n o = conc (pgList' n) (txt o)

-- footsect = delay $ (prefix ["", "-----"] footList)

-- vfill :: VObject
-- vfill = recurse (prefix ["|"])

-- f2 :: VObject
-- f2 = conc (blom 1) (footNote (conc (blom 2) (blom 3)))

-- f2a :: VObject
-- f2a = conc (blom 1) (conc (footNote (conc (blom 2) (blom 3))) (blom 4))

-- fn n =
--   footNote
--     (prefix ['(' : show n ++ ") This is a"] (singleton ["long footnote."]))

-- fn' n =
--   footNote
--     (conc
--         (singleton ['(' : show n ++ ") This is a"])
--         (singleton ["long footnote."]))

-- fn2 = conc (singleton ["Text"]) (fn 1)

-- fn2' :: VObject
-- fn2' = conc (singleton ["Text"]) (fn' 1)

-- fns = doc 8 (blom 1 # fn2)

-- fns' = doc 8 (blom 1 # fn2 # blom 2)

-- ps = doc 17 (purcell # purcell)

-- ps2 = (purcell # purcell)




------------------------------------------------------------------------
-- fooPrint = map (map putStrLn) . force

-- exPrint = sequence . concat $ fooPrint example



