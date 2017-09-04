module GalleyCode where 

import Control.Monad (sequence)

import qualified Text.PrettyPrint as P

import Prelude

import Debug.Trace 
    
testFoo :: (Show a) => a -> a
testFoo x = trace ("\nTesting Value: " ++ show x ++ "\n") x
fooBar :: (Show a) => String -> a -> a
fooBar str x = trace ("\n" ++ str ++ "  "++ show x ++ "\n") x

type Component = [String]

-- Tag , Direction , Object
-- type Galley = (String, Direction, Object)
data Galley = Galley 
            { tName :: String 
            , direction :: Direction
            , galleyObject :: Object
            } deriving (Show)

data Direction
  = Preceding
  | Following
  deriving (Show)

pageList = recurse (page #)

page = high 12 (target "TextPlace" # footSect)

footSect = delay $ prefix ["", "-----"] footList

footList = recurse (target "FootPlace" #)

text t = galley $ Galley "TextPlace" Preceding t

footNote f = galley $ Galley "FootPlace" Following f

type ShouldForce = Bool 
data Object = Object
  { eval           :: ShouldForce -> Constraint -> EvalResult
  , receive        :: ShouldForce -> Constraint -> Galley -> RcvResult
  , openTargets    :: [String]
  , delayedTargets :: [String]
  , height         :: Int
  } -- deriving Show

instance Show Object where
  show obj =
    "Open Targets: " ++
    (show $ openTargets obj) ++
    "Delayed Targets: " ++
    (show $ delayedTargets obj) ++ 
    "Object Height: " ++ (show $ height obj)

type RcvResult = (Bool, [Galley], Object)

targets o = openTargets o ++ delayedTargets o

data EvalResult
  = Disappearing
  | Suspended { obj  :: Object }
  | NoSpace   { obj  :: Object }
  | Sending   { gall :: [Galley]
              , obj  :: Object }
  | Yielding  { comp :: Component
              , obj  :: Object }

type Constraint = Maybe Int

force :: Object -> [Component]
force o =
  case eval o True Nothing of
    Disappearing -> []
    Yielding c o' -> c : force o'
    Sending gs o' -> force o'

nul :: Object
nul =
  Object
  { eval = (\forcing co -> Disappearing)
  , receive = (\forcing co g -> rcverror g "nul")
  , openTargets = []
  , delayedTargets = []
  , height = 0
  }

singleton :: Component -> Object
singleton c = o
  where
    o =
      Object
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

prefix :: Component -> Object -> Object
prefix c o = o'
  where
    o' =
      Object
      { eval =
          (\forcing co ->
              if co &? c
                then Yielding c o
                else NoSpace o')
      , receive =
          (\forcing co g -> thrdUpd3 (prefix c) $ receive o forcing (co &- c) g)
      , openTargets = openTargets o
      , delayedTargets = delayedTargets o
      , height = length c + height o
      }


thrdUpd3 :: (c -> d) -> (a, b, c) -> (a, b, d)
thrdUpd3 f (a, b, c) = (a, b, f c)

galley :: Galley -> Object
galley g =
  Object
  { eval = (\forcing co -> Sending [g] nul)
  , receive = (\forcing co g' -> rcverror g' "galley")
  , openTargets = []
  , delayedTargets = []
  , height = 0
  }

suffix :: Component -> Object -> Object
suffix c o = o'
  where
    o' =
      Object
      { eval =
          (\forcing co ->
              case eval o forcing (co &- c) of
                Disappearing -> eval (singleton c) forcing co
                r -> r {obj = suffix c (obj r)})
      , receive =
          (\forcing co g -> thrdUpd3 (suffix c) $ receive o forcing (co &- c) g)
      , openTargets = openTargets o
      , delayedTargets = delayedTargets o
      , height = length c + height o
      }

type OCState = (Bool, Object, Object)

type STfun s x = s -> (s, x)

type SToc = STfun OCState [Galley]

ocMkResult :: (OCState, [Galley]) -> RcvResult
ocMkResult ((rcv, o1, o2), gs) = (rcv, gs, o1 # o2)

ocGalleyFrom1, ocGalleyFrom2 :: Bool -> Constraint -> Galley -> SToc
ocGalleyFrom1 forcing co g@(Galley name Preceding _) s = (s, [g])
ocGalleyFrom1 forcing co g@(Galley name Following _) s@(rcv, o1, o2) =
  if name `notElem` targets o2
    then (s, [g])
    else let (rcv', gs2, o2') = receive o2 True (co &- o1) g
          in ocGalleysFrom2 forcing co gs2 (rcv || rcv', o1, o2')

ocGalleyFrom2 forcing co g@(Galley name Following _) s = (s, [g])
ocGalleyFrom2 forcing co g@(Galley name Preceding _) s@(rcv, o1, o2) =
  if name `notElem` targets o1
    then (s, [g])
    else let (rcv', gs1, o1') = receive o1 forcing (co &- o2) g
          in ocGalleysFrom1 forcing co gs1 (rcv || rcv', o1', o2)

stfold :: (a -> STfun b [c]) -> [a] -> STfun b [c]
stfold f [] s = (s, [])
stfold f (g:gs) s =
  let (s', gs') = f g s
      (s'', gs'') = stfold f gs s'
  in (s'', gs' ++ gs'')


-- Why two of the same function?
ocGalleysFrom1, ocGalleysFrom2 :: Bool -> Constraint -> [Galley] -> SToc
ocGalleysFrom1 forcing co = stfold (ocGalleyFrom1 forcing co)

ocGalleysFrom2 forcing co = stfold (ocGalleyFrom2 forcing co)

infixr 6 #
(#) :: Object -> Object -> Object
o1 # o2 = o
  where
    o =
      Object
      { eval = ocEval o1 o2
      , receive =
          (\forcing co g@(Galley name d o') ->
              let send1 =
                    let (r, gs, o1') = receive o1 forcing (co &- o2) g
                    in ocMkResult $ ocGalleysFrom1 forcing co gs (r, o1', o2)
                  send2 =
                    let (r, gs, o2') = receive o2 True (co &- o1) g
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

ocEval :: Object -> Object -> Bool -> Constraint -> EvalResult
ocEval o1 o2 forcing co =
  case eval o1 False (co &- o2) of
    Disappearing -> eval o2 forcing co
    NoSpace o1' -> NoSpace (o1' # o2)
    Yielding c o1' -> Yielding c (o1' # o2)
    Sending gs o1' ->
      case ocMkResult $ ocGalleysFrom1 False co gs (False, o1', o2) of
        (rcv, [], o') -> eval o' forcing co
        (rcv, gs, o') -> Sending gs o'
    Suspended o1' ->
      case eval o2 forcing (co &- o1') of
        Disappearing ->
          if forcing
            then eval o1' forcing co
            else Suspended o1'
        Suspended o2' -> Suspended (o1' # o2')
        NoSpace o2' ->
          if forcing
            then NoSpace o2'
            else Suspended (o1' # o2')
        Yielding c o2' -> eval (suffix c o1' # o2') forcing co
        Sending gs o2' ->
          case ocMkResult $ ocGalleysFrom2 False co gs (False, o1', o2') of
            (True, [], o') -> eval o' forcing co
            (False, [], o') -> error ("empty Sending???")
            (_, gs, o') -> Sending gs o'

strut h = replicate h ""

fill h c = take h (c ++ repeat "")

high :: Int -> Object -> Object
high h o = o'
  where
    eval' forcing =
      case eval o forcing (Just h) of
        NoSpace o1 -> Yielding (fill h ["@High: Object too large"]) nul
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
      Object
      { eval =
          (\forcing co ->
              case co of
                Nothing -> eval' forcing
                Just h' ->
                  if h' < h
                    then NoSpace o'
                    else eval' forcing)
      , receive =
          (\forcing co g -> thrdUpd3 (high h) $ receive o forcing (Just h) g)
      , openTargets = openTargets o
      , delayedTargets = delayedTargets o
      , height = h
      }

prefixConc :: Component -> Object -> Object
prefixConc c o = o'
  where
    o' =
      Object
      { eval =
          (\forcing co ->
              case eval o forcing (co &- c) of
                Disappearing -> Yielding c nul
                Yielding c' o2 -> Yielding (c ++ c') o2
                r -> r {obj = prefixConc c (obj r)})
      , receive =
          (\forcing co g ->
              if co &? c
                then thrdUpd3 (prefixConc c) $ receive o forcing (co &- c) g
                else (False, [forward g], o'))
      , openTargets = openTargets o
      , delayedTargets = delayedTargets o
      , height = length c + height o
      }

forward :: Galley -> Galley
forward (Galley name d o) = Galley name Following o

attach :: String -> Object -> Object
attach name = attach'
  where
    attach' o = o'
      where
        o' =
          Object
          { eval =
              (\forcing co ->
                  case eval o forcing Nothing of
                    Disappearing -> Disappearing
                    NoSpace o1 -> error "attach: NoSpace without constraints!"
                    Suspended o1 ->
                      if isEmpty co
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
              (\forcing co g -> thrdUpd3 attach' $ receive o forcing co g)
          , openTargets = openTargets o
          , delayedTargets = delayedTargets o
          , height = 0
          }

target :: String -> Object
target name = o
  where
    o =
      Object
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
                          then (True, [], (attach name o' # o))
                          else case eval o' False Nothing of
                                  Disappearing -> (True, [], o)
                                  Suspended o'' ->
                                    (True, [], (attach name o'' # o))
                                  NoSpace o'' ->
                                    error "target: NoSpace without constraint!"
                                  Sending gs1 o'' ->
                                    (True, gs1, (attach name o'' # o))
                                  Yielding c o'' ->
                                    if co &? c
                                      then let g' = Galley name' Following o''
                                               (rcv, gs1, o1) = receive
                                                                (prefix c o)
                                                                forcing
                                                                co
                                                                g'
                                          in (True, gs1, o1)
                                      else ( False
                                          , [Galley name Following $ prefix c o'']
                                          , nul))
      , openTargets = [name]
      , delayedTargets = []
      , height = 0
      }

recurse :: (Object -> Object) -> Object
recurse ff = o
  where
    ffo = ff o
    ff0 = ff nul -- List Of strings | openTargets o ++ delayedTargets o
    targs = targets ff0
    o =
      Object
      { eval =
          (\forcing co ->
              if forcing || isEmpty co || not (co &? ffo)
                then Disappearing
                else Suspended o)
      , receive =
          (\forcing co g@(Galley name d o') ->
              case co of
                Just 0 -> (False, [forward g], nul)
                _ ->
                  if name `elem` targs
                    then case receive ff0 forcing co g of
                          (False, gs, o1) -> (False, [forward g], nul)
                          r -> receive ffo forcing co g
                    else rcverror g "recurse")
      , openTargets = []
      , delayedTargets = targs
      , height = 0
      }

delay :: Object -> Object
delay o = o'
  where
    o' =
      Object
      { eval =
          (\forcing co ->
              if forcing || isEmpty co || not (co &? o)
                then Disappearing
                else Suspended o')
      , receive =
          (\forcing co g@(Galley name d o') ->
              case co of
                Just 0 -> (False, [forward g], nul)
                _ ->
                  if name `elem` targs
                    then case receive o forcing co g of
                          (False, gs, o1) -> (False, [forward g], nul)
                          r -> r
                    else rcverror g "delay")
      , openTargets = []
      , delayedTargets = targs
      , height = 0
      }
    targs = targets o

vExpand :: Object -> Object
vExpand o = o'
  where
    o' =
      Object
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
      , receive = (\frc co g -> thrdUpd3 vExpand (receive o frc co g))
      , openTargets = openTargets o
      , delayedTargets = delayedTargets o
      , height = height o
      }

recurseF :: ((a -> Object) -> (a -> Object)) -> (a -> Object)
recurseF ff = f
  where
    f' = ff f
    f a = o -- fooBar "o is called"  $
      where
        ffo = f' a
        ff0 = ff (const nul) a
        targs = targets ff0
        o =
          Object -- { as before }
          { eval =
              (\forcing co ->
                  if forcing || isEmpty co || not (co &? ffo)
                    then Disappearing
                    else Suspended o)
          , receive =
              (\forcing co g@(Galley name d o') ->
                  case co of
                    Just 0 -> (False, [forward g], nul)
                    _ ->
                      if name `elem` targs
                        then case receive ff0 forcing co g of
                              (False, gs, o1) -> (False, [forward g], nul)
                              r -> receive ffo forcing co g
                        else rcverror g "recurseF")
          , openTargets = []
          , delayedTargets = targs
          , height = 0
          }

-- npage :: Int -> Object
-- npage n =
--   high 14 $
--   prefix
--     ["          - " ++ show n ++ "-", ""]
--     (vExpand (target "TextPlace") # footSect)

-- npageList :: Object
-- npageList =
--   let f mkpl n = npage n # mkpl (n + 1)
--   in recurseF f 1 -- testFoo $ (    )
npage :: Int -> Object
npage = npage' 14

npage' :: Int -> Int -> Object
npage' bounds n =
  high bounds $
  prefix
    ["          - " ++ show n ++ "-", ""]
    (vExpand (target "TextPlace") # footSect)

npageList :: Object
npageList = npageList' 14 
npageList':: Int -> Object
npageList' bounds =
  let f mkpl n = npage' bounds n # mkpl (n + 1)
  in recurseF f 1 -- testFoo $ 


displayObject n wid o = putStr $ unlines $ frame n wid $ force o

frame n wid [] = []
frame n wid cs = overline (f cs1) ++ frame n wid cs2
  where
    (cs1, cs2) = splitAt n cs
    l2 s = l1 s ++ "|"
    l1 s = '|' : take wid (s ++ repeat ' ')
    b2 = [replicate (wid + 2) '-']
    b1 = [replicate (wid + 1) '-']
    p1 c = map l1 c ++ b1
    p2 c = map l2 c ++ b2
    f [] = []
    f [c] = p2 c
    f (c:cs) = zipWith (++) (p1 c) (f cs)
    overline l@(s:ss) = replicate (length s) '-' : l

printObject :: Object -> IO ()
printObject = putStr . string_of_Object True

printObject' = putStr . string_of_Object False

string_of_Object :: Bool -> Object -> String
string_of_Object forcing = f 10 []
  where
    f 0 gs o = "<<<Terminating.>>>\n"
    f n gs o =
      let printstray gs =
            unlines
              ("====================" :
                map string_of_stray_galley gs ++ ["####################"])
      in case eval o forcing Nothing of
            Disappearing -> "<<<Disappearing>>>\n" ++ printstray gs
            Suspended o' ->
              "<<<Suspended!!!>>>\n" ++
              printstray gs ++
              case gs of
                [] -> f (n - 1) [] o'
                (g@(Galley name d og):gs1) ->
                  if name `elem` targets o'
                    then case receive o' False Nothing g of
                          (False, gs2, o2) ->
                            "<<<NoSpaceR>>>\n" ++ f (n - 1) (gs1 ++ gs2) o2
                          (True, gs2, o2) ->
                            "<<<Received " ++
                            name ++ ">>>\n" ++ f n (gs1 ++ gs2) o2
                    else f n gs1 o'
            Sending gs' o' ->
              "<<<Sending!!!>>>\n" ++
              printstray gs' ++
              case gs ++ gs' of
                [] -> f (n - 1) [] o'
                (g@(Galley name d og):gs1) ->
                  if name `elem` targets o'
                    then case receive o' False Nothing g of
                          (False, gs2, o2) ->
                            "<<<NoSpaceR>>>\n" ++ f (n - 1) (gs1 ++ gs2) o2
                          (True, gs2, o2) ->
                            "<<<Received " ++
                            name ++ ">>>\n" ++ f n (gs1 ++ gs2) o2
                    else f n gs1 o'
            NoSpace o' -> "<<<NoSpace --- continuing>>>\n" ++ f n gs o'
            Yielding c o' -> string_of_Component c ++ f n gs o'

string_of_stray_galley (Galley name d o) =
  "No target for galley `" ++
  name ++
  "&&" ++
  show d ++
  "; h=" ++
  show (height o) ++
  "\n" ++
  string_of_Object True o ++
  "~~~~~~~~~~ end of galley `" ++ name ++ "&&" ++ show d ++ "\n"

string_of_Component c = unlines (map ('|' :) c ++ ["--------------------"])

isEmpty :: Constraint -> Bool
isEmpty Nothing = False
isEmpty (Just 0) = True
isEmpty _ = False

class Constrainer c where
  cHeight :: c -> Int

(&-) :: Constrainer c => Constraint -> c -> Constraint
Nothing &- c = Nothing
(Just h) &- c
  | h' < 0 = Just 0
  | otherwise = Just h'
  where
    h' = h - cHeight c

(&?) :: Constrainer c => Constraint -> c -> Bool
Nothing &? c = True
(Just h) &? c = h >= cHeight c

instance Constrainer Int where
  cHeight n = n

instance Constrainer Object where
  cHeight o = height o

instance Constrainer c => Constrainer (Maybe c) where
  cHeight Nothing = 0
  cHeight (Just o) = cHeight o

class IsChar c where
  ischar :: c

instance IsChar Char where
  ischar = '?'

class IsString s where
  isstring :: s

instance IsChar a => IsString [a] where
  isstring = [ischar]

instance IsString a => Constrainer [a] -- Component only!
                                                          where
  cHeight c = length c

rcverror g s = error ("Cannot receive: " ++ s ++ "\n" ++ show g)

blom n =
  singleton
    ["(" ++ show n ++ ") Blom, Eric. Some", "Great Composers.", "Oxford, 1944."]

heading n = prefix ["PURCELL(" ++ show n ++ ")"] $ footNote (blom n)

purcell = heading 1 # body

body = foldr prefix nul bodycs

body2 = foldr prefix nul (bodycs ++ bodycs)

-- bodycs = exHori 25
  -- [ [""]
  -- , ["In the world of music", "England is supposed to be"]
  -- , ["a mere province.  If she"]
  -- , ["produces an indifferent"]
  -- , ["composer or performer,"]
  -- , ["that is regarded"]
  -- , ["elsewhere as perfectly", "normal and natural; but"]
  -- , ["if foreign students of"]
  -- , ["musical history have to"]
  -- , ["acknowledge a British"]
  -- , ["musical genius, he is", "considered a freak."]
  -- , [""]
  -- , ["    Such a freak is", "Henry Purcell.  Yet if we"]
  -- , ["make a choice of fifteen"]
  -- , ["of the world's musical"]
  -- , ["classics, as here, we find"]
  -- , ["that we cannot omit this", "English master."]
  -- ]

bodycs = [
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

example = pageList # text purcell

nexample = npageList # text purcell

h2a = heading 1 # heading 2

conc o1 o2 = o1 # o2

h3a = conc (heading 1) (conc (heading 2) (heading 3))

h3'npl = conc npageList (text h3a)

bp = conc npageList (text (conc (conc (blom 1) body) purcell))

bh = conc npageList (text (conc (blom 1) (conc body (heading 2))))

pg' n = high n $ conc (vExpand (target "TextPlace")) footsect

pg n = high n $ conc (target "TextPlace") footsect

pgList' n = recurse (conc (pg' n))

pgList n = recurse (conc (pg n))

doc n o = conc (pgList n) (text o)

doc' n o = conc (pgList' n) (text o)

footsect = delay $ (prefix ["", "-----"] footList)

vfill = recurse (prefix ["|"])

f2 = conc (blom 1) (footNote (conc (blom 2) (blom 3)))

f2a = conc (blom 1) (conc (footNote (conc (blom 2) (blom 3))) (blom 4))

fn n =
  footNote
    (prefix ['(' : show n ++ ") This is a"] (singleton ["long footnote."]))

fn' n =
  footNote
    (conc
        (singleton ['(' : show n ++ ") This is a"])
        (singleton ["long footnote."]))

fn2 = conc (singleton ["Text"]) (fn 1)

fn2' = conc (singleton ["Text"]) (fn' 1)

fns = doc 8 (blom 1 # fn2)

fns' = doc 8 (blom 1 # fn2 # blom 2)

ps = doc 17 (purcell # purcell)

ps2 = (purcell # purcell)




------------------------------------------------------------------------
fooPrint = map (map putStrLn) . force

exPrint = sequence . concat $ fooPrint example

main = do
  putStrLn ""
  let res = force example
  putStr $ renderComp res

render = P.render

type Doc = P.Doc

vcat = P.vcat

hcat = P.hcat

renderComp compList = render . P.vcat $ docCompList
  where
    docCompList = P.punctuate (P.text "\n\n") docCompList'
    docCompList' = map prettyComponent compList

prettyComponent :: Component -> Doc
prettyComponent cmp = vcat $ map P.text cmp