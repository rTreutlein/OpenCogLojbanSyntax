{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE RelaxedPolyRec             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE RankNTypes #-}

module OpenCog.Lojban.Syntax where

import Prelude hiding (id,(.),(<*>),(<$>),pure,(*>),(<*),foldl)

import qualified Data.List.Split as S
import Data.Maybe (fromJust)
import Data.Hashable

import System.Random

import Control.Monad.Trans.Reader
import Control.Category (id,(.))
import Control.Isomorphism.Partial
import Control.Isomorphism.Partial.Derived
import Control.Isomorphism.Partial.Unsafe
import Text.Syntax

import OpenCog.AtomSpace (Atom(..),TruthVal(..),noTv,stv,atomFold,nodeName)
import OpenCog.Lojban.Util

import OpenCog.Lojban.Syntax.Types
import OpenCog.Lojban.Syntax.Util
import OpenCog.Lojban.Syntax.AtomUtil

import Debug.Trace

mytrace a = traceShow a a
mytrace2 s a = trace (s ++(' ':show a)) a

--Todo
-- quantifiers

-------------------------------------------------------------------------------
--Sumti
-------------------------------------------------------------------------------

_LE = reorder0 <$> selmaho "LE"

--Handles anykind of LE phrases
-- State ((le,(s,(v,[a]))),Int)
-- State (le,((s,(v,[a]))),Int))
--TODO: handle distinctions of different words in LE
leP :: SyntaxReader (State Atom)
leP = collapsState .< (choice mfg gfm .> first (_ssl .> handleBE)) . inverse associate
    <$> withSeedState (_LE
                      <&> selbriUI
                      <&> pureVarNode
                      <&> optState beP
                      <* optSelmaho "KU")
    where pureVarNode :: SyntaxReader (State Sumti)
          pureVarNode = pure ((Node "VariableNode" "$var" noTv,Nothing),[])

          --Handles addtional arguments in a leP
          beP :: SyntaxReader (State [Sumti])
          beP = first cons <$>            sepSelmaho "BE"  *> sumtiAll
                           <&> stateMany (sepSelmaho "BEI" *> sumtiAll)
                                       <* optSelmaho "BEhO"

          handleBE :: Iso (Sumti,Maybe [Sumti]) [Sumti]
          handleBE = (cons ||| tolist1) . ifJustB


mfg :: (String,(Atom,Int)) -> Iso (String,(Atom,Int)) (State Atom)
mfg ("le" ,_)  = genInstance "IntensionalInheritanceLink" . rmfst "le"
mfg ("lo" ,_)  = genInstance "InheritanceLink"            . rmfst "lo"
mfg ("lei",_)  = massOf "IntensionalInheritanceLink"      . rmfst "lei"
mfg ("loi",_)  = massOf "InheritanceLink"                 . rmfst "loi"
mfg ("le'i",_) = setOf "IntensionalInheritanceLink"       . rmfst "le'i"
mfg ("lo'i",_) = setOf "InheritanceLink"                  . rmfst "lo'i"
--TODO make typical have higer TV?
mfg ("le'e",_) = genInstance "IntensionalInheritanceLink" . rmfst "le'e"
mfg ("lo'e",_) = genInstance "InheritanceLink"            . rmfst "lo'e"
mfg (a,_) = error $ "mfg can't handle " ++ a

gfm :: State Atom -> Iso (String,(Atom,Int)) (State Atom)
gfm (a,s) = case (isint,ismas,isset) of
    (True ,False,False) -> genInstance "IntensionalInheritanceLink". rmfst "le"
    (False,False,False) -> genInstance "InheritanceLink"           . rmfst "lo"
    (True ,True,False)  -> massOf "IntensionalInheritanceLink"     . rmfst "lei"
    (False,True,False)  -> massOf "InheritanceLink"                . rmfst "loi"
    (True ,False,True)  -> setOf "IntensionalInheritanceLink"      . rmfst "le'i"
    (False,False,True)  -> setOf "InheritanceLink"                 . rmfst "lo'i"
    where defs  = getDefinitons [a] s
          isint = any (\case { (Link "IntensionalInheritanceLink" _ _) -> True
                            ; _ -> False}) defs
          ismas = any (\case { (Link "EvaluationLink" _ _) -> True
                            ; _ -> False}) defs
          isset = any (\case { (Link "SetTypeLink" _ _) -> True
                            ; _ -> False}) defs

massOf :: String -> Iso (Atom,Int) (State Atom)
massOf itype = instanceOf =. (first _ssl . addStuff <. (implicationOf *^* genInstance itype)) . reorder

    where pred = ((noTv,Node "PredicateNode" "gunma" noTv),tag)
          pp = Node "PredicateNode" "gunma" noTv
          arg1 = (Node "VariableNode" "$var" noTv,tag)
          tag = Nothing

          reorder = Iso (Just . f) (Just . g) where
              f (a,i)     = (((pp,i),(a,i)),[])
              g ((_,m),_) = m

          addStuff = Iso (Just . f) (Just . g) where
              f (p,a) = ((((noTv,p),tag),[arg1,(a,tag)]),0)
              g ((((_,p),_),[_,(a,_)]),_) = (p,a)


setOf :: String -> Iso (Atom,Int) (State Atom)
setOf itype = setTypeL . tolist2 . makeSet <. genInstance itype
    where makeSet = Iso (Just . f) (Just . g)
              where f a = let salt = show a
                              set  = cCN (randName 1 salt) noTv
                          in (set,a)
                    g (_,a) = a

--Handle anykind of LA phrase
laP :: SyntaxReader (State Atom)
laP = handleName . first concept <$> withSeed (between (sepSelmaho "LA")
                                                       (optSelmaho "KU")
                                                       anyWord
                                              )
    where handleName :: Iso (Atom,Int) (State Atom)
          handleName = Iso (\(a,i) -> let c = cCN (randName i (nodeName a)) lowTv
                                          p = cPN "cmene" lowTv
                                          l = cEvalL highTv p (cLL [a,c])
                                      in Just (c,[l]))
                           (\(_,[EvalL _ (LL [a,_])]) -> Just (a,0))

liP :: SyntaxReader (Atom,[Atom])
liP = sepSelmaho "LI" *> (xo <|> pa) <* optSelmaho "LOhO"

xo :: SyntaxReader (State Atom)
xo = reorder0 . varnode <$> word "xo"

pa :: SyntaxReader (State Atom)
pa = reorder0
    . (         number       |||    concept   )
    . (showReadIso . paToNum |^| isoConcat " ")
    <$> many1 (joiSelmaho "PA")
    where paToNum :: Iso [String] Int
          paToNum = foldl (digitsToNum . second paToDigit) . addfst 0

          digitsToNum :: Iso (Int,Int) Int
          digitsToNum = Iso f g where
              f (i,j) = Just (i*10+j)
              g 0     = Nothing
              g n     = Just (n `div` 10,n `mod` 10)

          paToDigit :: Iso String Int
          paToDigit = mkSynonymIso [("no",0),("pa",1)
                                   ,("re",2),("ci",3)
                                   ,("vo",4),("mu",5)
                                   ,("xa",6),("ze",7)
                                   ,("bi",8),("so",9)]


--KohaPharse for any kind of Pro-Noune
kohaP :: SyntaxReader (Atom,[Atom])
kohaP = reorder0 <$> (ma <|> koha)
    where koha = concept <$> selmaho "KOhA"
          ma   = varnode <$> word "ma"

--This Handles relative phrases
noiP :: SyntaxReader (State Atom)
noiP = sepSelmaho "NOI" *> bridi <* optSelmaho "KUhO"

goiP :: SyntaxReader (State Atom)
goiP = ptp (selmaho "GOI") goiToNoi noiP
    where goiToNoi = mkSynonymIso [("pe"  ,"poi ke'a srana ")
                                  ,("po"  ,"poi ke'a se steci srana ")
                                  ,("po'e","poi jinzi ke se steci srana ")
                                  ,("po'u","poi du ")
                                  ,("ne"  ,"noi ke'a srana ")
                                  ,("no'u","noi du ")]

--This handles unconected sumti with optional relative phrases
sumti :: SyntaxReader (State Atom)
sumti = kohaP <|> leP <|> laP <|> liP

sumtiNoi :: SyntaxReader (State Atom)
sumtiNoi = (kehaToSesku  ||| id) . reorder <$> sumti
                                           <&> optState (noiP <|> goiP)
    where reorder = Iso (Just . f) (Just . g)
          f ((a,Just n ),s) = Left (a,n:s)
          f ((a,Nothing),s) = Right (a,s)
          g (Left (a,n:s))  = ((a,Just n ),s)
          g (Right (a,s))   = ((a,Nothing),s)
          --If we have a relative clause
          --this will switch the ke'a with the actually concept
          --TODO: Do we always have a ke'a in a relative clause?
          kehaToSesku :: Iso (State Atom) (State Atom)
          kehaToSesku = Iso f g
              where f (c,l) = let nl = map (switch kea c) l
                              in if nl == l
                                  then Just (c,nl)
                                  else Nothing
                    g (c,l) = let nl = map (switch c kea) l
                              in if nl == l
                                  then Just (c,nl)
                                  else Nothing
                    kea = Node "ConceptNode" "ke'a" noTv
                    switch a b l@(InhL [x,c] tv) = if c == a
                                                  then cInhL tv x b
                                                  else l
                    switch _ _ l = l

sumtiLaiP :: SyntaxReader (State Atom)
sumtiLaiP = ptp (pa <*> selbri) id (ptp pa addLE sumtiLai) <|> sumtiLai
    where addLE = Iso (Just . f) (Just . g)
          f s = s ++ " lo "
          g s = take (length s - 4) s

sumtiLai :: SyntaxReader (State Atom)
sumtiLai = collapsState
           . first ((instanceWithSize ||| reorder0) . reorder)
           <$> withSeedState (optState pa <&> sumtiNoi)

    where reorder = Iso (Just . f) (Just . g)
              where f ((Just pa,sumti),seed)   = Left ((pa,seed),sumti)
                    f ((Nothing,sumti),_)      = Right sumti
                    g (Left ((pa,seed),sumti)) = ((Just pa,sumti),seed)
                    g (Right  sumti)           = ((Nothing,sumti),0)

          instanceWithSize :: Iso ((Atom,Int),Atom) (State Atom)
          instanceWithSize = second (tolist2 . (sizeL *** setTypeL)) . makeSet
              where makeSet = Iso (Just . f) (Just . g)
                    f ((a,i),b) = let salt = show a ++ show b
                                      set  = cCN (randName i salt) noTv
                                  in (set,([set,a],[set,b]))
                    g (_,([_,a],[_,b])) = ((a,0),b)


--This Handels Sumti connected by logical connectives
sumtiC :: SyntaxReader (State Atom)
sumtiC = first ( (conLink . reorder ||| id) . ifJustB)
        <$> sumtiLaiP <&> optState (_A <&> sumtiC)
    where _A = reorder0 <$> selmaho "A"
          reorder = Iso (\(a1,(con,a2)) -> Just (con,[a1,a2]))
                        (\(con,[a1,a2]) -> Just (a1,(con,a2)))

sumtiT :: SyntaxReader (State Sumti)
sumtiT =  first handleFA <$> optState _FA
                         <&> sumtiC
    where handleFA = commute . first (isofmap faToPlace)
          _FA = reorder0 <$> selmaho "FA"

          faToPlace :: Iso String String
          faToPlace = mkSynonymIso [("fa","1")
                                   ,("fe","2")
                                   ,("fi","3")
                                   ,("fo","4")
                                   ,("fu","5")]
modalSumti :: SyntaxReader (State Sumti)
modalSumti = reorder . first handleFIhO <$> (fihoP <|> baiP)
                                        <&> sumtiT
    where handleFIhO = (fi'otag &&& _frame) . second (inverse tolist1)
                                            . handleTAG . second tolist1
          fi'otag = Iso (Just . f) (Just . g)
              where f ((tv,PN name),(s,tag)) = (s,Just $ name++tag++ show tv)
                    g (s,Just nametag) =
                        let [name,tag,tv] = S.split (S.oneOf "12345") nametag
                        in ((read tv,cPN name lowTv),(s,tag))
          reorder = Iso (\((a,b),c) -> Just (a,b: c))
                        (\ (a,b: c) -> Just ((a,b),c))

          fihoP :: SyntaxReader (State (Tagged Selbri))
          fihoP = sepSelmaho "FIhO" *> selbriUI <* optSelmaho "FEhU"

          baiP :: SyntaxReader (State (Tagged Selbri))
          baiP = ReaderT (\wl@(_,_,btf,_) -> runReaderT (bai btf) wl)
              where bai btf = ptp syn (iso btf) selbriUI
                    iso btf = mkSynonymIso btf . stripSpace
                    syn     = optional (selmaho "SE") <*> selmaho "BAI"


sumtiAll :: SyntaxReader (State Sumti)
sumtiAll = filterState <$> modalSumti <|> sumtiT

sumtiAllUI :: SyntaxReader (State Sumti)
sumtiAllUI = withAttitude sumtiAll

-------------------------------------------------------------------------------
--Selbri
-------------------------------------------------------------------------------

gismuP :: SyntaxReader (State Atom)
gismuP = implicationOf . first predicate <$> withSeed gismu

tanru :: SyntaxReader (State Atom)
tanru = handleTanru <$> gismuP
                    <&> optState tanru
    where handleTanru = (second (cons . first _iil) ||| id ) . reorder
          reorder = Iso (Just . f) (Just . g)
          f ((g,Just t),s)  = Left (g,((t,g),s))
          f ((g,Nothing),s) = Right (g,s)
          g (Left (g,((t,_),s)))  = ((g,Just t),s)
          g (Right (g,s))         = ((g,Nothing),s)


--meP :: SyntaxReader (State Atom)
--meP =  handleME <$> selmaho "ME" <*> sumtiAll <*> optSelmaho "MEhU"

nuP :: SyntaxReader (Atom,[Atom])
nuP = handleNU <$> sepSelmaho "NU" *> withText bridi <* optSelmaho "KEI"
    where handleNU :: Iso ((Atom,[Atom]),String) (Atom,[Atom])
          handleNU = Iso f g where
              f ((atom,as),name) = let pred = cPN name lowTv
                                       link = mkCtxPre pred atom
                                   in Just (pred,link:as)
              g (PN name,CtxPred atom : as) = Just ((atom,as),name)
              g _ = Nothing

_NAhE :: SyntaxReader (State TruthVal)
_NAhE = reorder0 . naheToTV <$> (selmaho "NAhE" <|> pure "")
    where naheToTV = mkSynonymIso [("je'a",stv 1    0.9)
                                  ,(""    ,stv 0.75 0.9)
                                  ,("no'e",stv 0.5  0.9)
                                  ,("na'e",stv 0.25 0.9)
                                  ,("to'e",stv 0    0.9)]


selbri :: SyntaxReader (State (Tagged Atom))
selbri = filterState . first commute . associate <$> optional (selmaho "SE")
                                                  <*> (tanru <|> nuP)
selbriP :: SyntaxReader (State (Tagged Selbri))
selbriP = first associate <$> _NAhE <&> selbri

selbriUI :: SyntaxReader (State (Tagged Selbri))
selbriUI = collapsState . first ((merge . first (second handleUI) ||| id) . reorder)
        <$> withSeedState (selbriP <&> optState uiP)
    where reorder = Iso (Just . f) (Just . g)
              where f ((((tv,p),t),Just ui),i)    = Left  ((tv,((ui,p),i)),t)
                    f ((p,Nothing),i)             = Right (p,[])
                    g (Left  ((tv,((ui,p),i)),t)) = ((((tv,p),t),Just ui),i)
                    g (Right (p,_))               = ((p,Nothing),0)
          merge = Iso (Just . f) (Just . g)
              where f ((tv,(a,s)),t) = (((tv,a),t),s)
                    g (((tv,a),t),s) = ((tv,(a,s)),t)


-------------------------------------------------------------------------------
--bacru
-------------------------------------------------------------------------------

_PU :: SyntaxReader (State Atom)
_PU = reorder0 . concept <$> selmaho "PU"

_ZI :: SyntaxReader (State Atom)
_ZI = reorder0 . concept <$> selmaho "ZI"

_trati :: SyntaxReader (State (Maybe Atom))
_trati = first handleTrati <$> stateMany (_PU <|> _ZI)
    where handleTrati = Iso (Just . f) (Just . g)
          f [] = Nothing
          f [x]= Just x
          f xs = apply andl xs
          g Nothing   = []
          g (Just xs@(AL _)) = fromJust $ unapply andl xs
          g (Just x) = [x]

_NA :: SyntaxReader (State String)
_NA = reorder0 <$> selmaho "NA"

--THis Handles compelte sentences
-- Remark: Handle the modal Sumti before handleBRIDI
bridi :: SyntaxReader (Atom,[Atom])
bridi = handleBRIDI . first mergeSumti <$> stateMany1 sumtiAll
                                       <*   optext "cu"
                                       <&> _trati
                                       <&> optState _NA
                                       <&> selbriUI
                                       <&> stateMany sumtiAll

-- (a,(mp,(ma,(s,aa))))
-- (mp,(ma,(s,a++aa)))
-- ((mp,(ma,(s,a))),as)
-- (bridi,as)

handleBRIDI :: Iso ((Maybe Atom,(Maybe String,(Tagged Selbri,[Sumti]))),[Atom]) (Atom,[Atom])
handleBRIDI = first $ handleNA
                    . second _ctx
                    . inverse associate
                    . first commute
                    . second _frames
                    . associate

-- ((MPU,(MNA,(Selbri,Args)))   ,Atoms)
-- (((MPU,MNA),(Selbri,Args))   ,Atoms)
-- (((MPU,MNA),frames)            ,Atoms)
-- (((MNA,MPU),frames)            ,Atoms)
-- ((MNA,(MPU,frames))            ,Atoms)
-- ((MNA,MCtxL)                 ,Atoms)
-- (bridi                       ,Atoms)

handleNA :: Iso (Maybe String,Atom) Atom
handleNA = Iso f g where
    f (Nothing,a)    = Just a
    f (Just n, a)    = apply _eval (cGPN n lowTv,[a])
    g (EvalL (GPN n) a) = Just (Just n,a)
    g a = Just (Nothing,a)

--For mergin sumties before and after the selbri into a single list
mergeSumti :: (a ~ aa) => Iso ([a],(pu,(na,(s,[aa])))) (pu,(na,(s,[a])))
mergeSumti = Iso f g where
    f (a1,(pu,(na,(s,a2)))) = Just (pu,(na,(s,a1++a2)))
    g     (pu,(na,(s,a)))   = case a of
                                   [] -> Nothing
                                   (x:xs) -> Just ([x],(pu,(na,(s,xs))))


bridiUI :: SyntaxReader (State Atom)
bridiUI = collapsState . (first handleUI ||| id) . reorder . expandState
        <$> withSeed (optState uiP <&> bridi)
    where reorder = Iso (Just . rf) (Just . rg)
          rf (((Just ui,b),i),s)   = Left  (((ui,b),i),s)
          rf (((Nothing,b),i),s)   = Right ((b,[]),s)
          rg (Left (((ui,b),i),s)) = (((Just ui,b),i),s)
          rg (Right((b,_),s)     ) = (((Nothing,b),0),s)


preti :: SyntaxReader Atom
preti = ((_satl . associate) ||| handleMa) . ifJustA <$> optional (string "xu") <*> bridiUI
    where handleMa =
              Iso (\(a,s) ->
                    let x = atomFold (\r a -> r || isMa a) False a
                        isMa (Node "VariableNode" x noTv) = x /= "$var"
                        isMa _ = False
                        all = Link "ListLink" (a:s) noTv
                        na = Link "PutLink" [all,Link "GetLink" [all] noTv] noTv
                    in Just (x ? na $ all))
                  (\ma -> case ma of
                      (Link "PutLink"  [LL (a:s),_] _) -> Just (a,s)
                      (Link "ListLink" (a:s) _) -> Just (a,s))


------------------------------------
--Attitude
-----------------------------------

_UI :: SyntaxReader Atom
_UI = concept <$> selmaho "UI"

_CAI :: SyntaxReader String
_CAI = selmaho "CAI"

_NAI :: SyntaxReader String
_NAI = selmaho "NAI"

caiP :: SyntaxReader TruthVal
caiP = naicaiToTV . isoConcat "|" . tolist2 <$> (_NAI <|> pure "")
                                            <*> (_CAI <|> pure "")

naicaiToTV :: Iso String TruthVal
naicaiToTV = mkSynonymIso [("|cai"    ,stv 1     0.9)
                          ,("|sai"    ,stv 0.833 0.9)
                          ,("|"       ,stv 0.75  0.9)
                          ,("|ru'e"   ,stv 0.666 0.9)
                          ,("|cu'i"   ,stv 0.5   0.9)
                          ,("nai|ru'e",stv 0.333 0.9)
                          ,("nai|sai" ,stv 0.166 0.9)
                          ,("nai|cai" ,stv 0     0.9)]


uiP :: SyntaxReader (State (Atom,TruthVal))
uiP = reorder0 <$> _UI <*> caiP

withAttitude :: SyntaxReader (State Sumti) -> SyntaxReader (State Sumti)
withAttitude syn = merge . first ((first handleUI ||| id) . reorder) . expandState
                <$> withSeed (syn <&> optState uiP)
    where reorder = Iso (Just . rf) (Just . rg)
          rf (((a,mt),Just ui),i)   = Left (((ui,a),i),mt)
          rf (((a,mt),Nothing),i)   = Right ((a,[]),mt)
          rg (Left (((ui,a),i),mt)) = (((a,mt),Just ui),i)
          rg (Right ((a,_),mt)    ) = (((a,mt),Nothing),0)
          merge = Iso (Just . mf) (Just . mg)
          mf (((a,s1),mt),s2) = ((a,mt),s1++s2)
          mg ((a,mt),s)       = (((a,s),mt),s)

handleUI :: Iso (((Atom,TruthVal),Atom),Int) (State Atom)
handleUI = second (cons . first _frames . joinState
                        . (selbri *** (sumti1 *** (sumti2 *** sumti3))))
                     . reorder
    where joinState = Iso (Just . jf) (Just . jg)
          jf ((tv,(a1,s1)),((a2,s2),((a3,s3),(a4,s4)))) = ((((tv,a1),Nothing),[a2,a3,a4]),s1++s2++s3++s4)
          jg ((((tv,a1),_),[a2,a3,a4]),s) = ((tv,(a1,s)),((a2,s),((a3,s),(a4,s))))
          reorder = Iso (Just . rf) (Just . rg)
          rf (((ui,tv),a),i) = (a,((tv,((),i)),(((),i),((ui,i),(a,i)))))
          rg (a,((tv,((),_)),(((),_),((ui,_),(_,_))))) = (((ui,tv),a),0)
          sumti3 = first (addsnd $ Just "3") . instanceOf
          sumti2 = first (addsnd $ Just "2") . instanceOf
          sumti1 = first (addsnd $ Just "1") . instanceOf
                    . first (insert (Node "ConceptNode" "mi" noTv))
          selbri = second ( instanceOf
                          . first (insert (Node "PredicateNode" "cinmo" noTv))
                          )

------------------------------------
--Pre Parse XXX would need to consider all words to not parse things it shouldnt'
-----------------------------------

{-preParser :: SyntaxReader String
preParser =  isoConcat "" . tolist2
          <$> ((preGOI <|> prePA <|> (tolist1 <$> token)) <*> preParser)
          <|> (pure "")

preGOI :: SyntaxReader String
preGOI = goiToNoi <$> selmaho "GOI"
    where goiToNoi = mkSynonymIso [("pe"  ,"poi ke'a srana ")
          ,("po"  ,"poi ke'a se steci srana ")
          ,("po'e","poi jinzi ke se steci srana ")
          ,("po'u","poi du ")
          ,("ne"  ,"noi ke'a srana ")
          ,("no'u","noi du ")]

prePA :: SyntaxReader String
prePA = ptp (pa <*> selbri) id (addLE . isoConcat "" <$> many1 (joiSelmaho "PA"))
    where addLE = Iso (Just . f) (Just . g)
          f s = s ++ " lo "
          g s = take (length s - 4) s

-}

{-
andExpansion :: Iso Atom Atom
andExpansion = Iso (\a -> atomMap a)

eval (Link "EvaluationLink" e _)

data Linked a b = NotLinked a | Linked a b (Linked a b)
addElem :: a -> Linked a b -> Linked a b
addElem e (NotLinked a)    = NotLinked (a:e)
addElem e (Linked a b l) = Linked (a:e) b $ addElem e l

addLink :: s -> Linked a b -> Linked a b
addLink e (NotLinked a) = Linked a e a
addLink e (Linked a b l) = Linked a b $ addLink e l

func :: Linked [Atom] String -> Atom -> Linked [Atom] String
func al@(NotLinked a) (Link "AndLink" [e1,e2] noTv) = Linked (a:e1) "AndLink" $ addElem e2 al
func al@(Linked a1 b l) (Link "AndLink" [e1,e2] noTv) =
    Linked (a1:e1) "AndLink" $ addElem e2 al
func l b = addElem b l
-}
