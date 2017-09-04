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
  "Object Width: " ++ (show $ width obj)
instance Constrainer HObject where
cDim = width
instance GalleyComponent HObject where
evaluateGC       = heval          
receiveGC        = hreceive       
openTargetsGC    = hopenTargets   
delayedTargetsGC = delayedTargets
dimGC            = cDim  
nul = HObject
    { heval = (\forcing co -> Disappearing)
    , hreceive = (\forcing co g -> rcverror g "nul")
    , hopenTargets = []
    , hdelayedTargets = []
    , width = 0
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
      , width = length c
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
      , width = length c + width o
      }
galley g =
  HObject
  { heval = (\forcing co -> Sending [g] nul)
  , hreceive = (\forcing co g' -> rcverror g' "galley")
  , hopenTargets = []
  , hdelayedTargets = []
  , width = 0
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
      , width = length c + width o
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
      , width = width o1 + width o2
      }
hhigh h o = o'
  where
    eval' forcing =
      case heval o forcing (Just h) of
        NoSpace o1 -> Yielding (fill h ["@High: HObject too large"]) nul
        Disappearing -> Yielding (strut h) nul
        Suspended o1 -> Suspended (hhigh h o1)
        Sending gs o1 -> Sending gs (hhigh h o1)
        Yielding c o1 ->
          let h' = h - length c
          in if h' < 0
                then error "@High: yielded component too hhigh!"
                else case heval (hhigh h' o1) forcing Nothing of
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
          (\forcing co g -> updateRcvResult (hhigh h) $ hreceive o forcing (Just h) g)
      , hopenTargets = hopenTargets o
      , hdelayedTargets = hdelayedTargets o
      , width = h
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
      , width = length c + width o
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
          , width = 0
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
                                                 receive
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
      , width = 0
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
      , width = 0
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
      , width = 0
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
      , width = width o
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
          , width = 0
          }
prepareComp _ = hcat left