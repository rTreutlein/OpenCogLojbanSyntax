{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE RelaxedPolyRec             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE RankNTypes                 #-}

module OpenCog.Lojban.Syntax where

import Prelude hiding (id,(.),(<*>),(<$>),pure,(*>),(<*),foldl)
import qualified Prelude as P
import Data.Char
--import Data.Foldable
import qualified Data.Foldable as F
import Data.List (partition,isPrefixOf,nub,any,intercalate)
import qualified Data.List.Split as S
import Data.Maybe (fromJust)
import System.IO.Unsafe
import qualified Control.Arrow as A
import Control.Monad.Trans.Reader
import qualified Data.Map as M
import Data.Functor.Identity

import Control.Category (id,(.))
import Control.Isomorphism.Partial
import Control.Isomorphism.Partial.Derived
import Control.Isomorphism.Partial.Unsafe
import Control.Isomorphism.Partial.TH
import Text.Syntax

import OpenCog.AtomSpace
import OpenCog.Lojban.Util

import Debug.Trace

mytrace a = traceShow a a
mytrace2 s a = trace (s ++(' ':show a)) a

--Todo
-- quantifiers

--The firs element of the tuple is a Atom that is part of the main Sentence/Link
--The List are other atoms which have to be added to the Atomspace or are needed for printing
type State a = (a,[Atom])
type Tag = String
type Sumti = Tagged Atom
type Selbri = (String,Atom) --STring represents TV
type Tagged a = (a,Maybe Tag)

type WordList = (M.Map String [String],[String],[(String,String)])
type SyntaxReader a = forall delta. Syntax delta => ReaderT WordList delta a

isofmap iso = Iso f g where
    f = Just . fmap (fromJust . apply iso)
    g = Just . fmap (fromJust . unapply iso)

instance IsoFunctor f => IsoFunctor (ReaderT a f) where
    iso <$> r
        = ReaderT (\e -> iso <$> runReaderT r e)

instance ProductFunctor f => ProductFunctor (ReaderT a f) where
    a <*> b
        = ReaderT (\e -> runReaderT a e <*> runReaderT b e)

instance Alternative f => Alternative (ReaderT a f) where
    a <|> b
        = ReaderT (\e -> runReaderT a e <|> runReaderT b e)
    a <||> b
        = ReaderT (\e -> runReaderT a e <||> runReaderT b e)
    empty = ReaderT (const empty)

instance Syntax f => Syntax (ReaderT a f) where
    pure x = ReaderT (\e -> pure x)
    token  = ReaderT (const token)
    withText r = ReaderT (withText . runReaderT r)
    ptp r1 iso r2 = ReaderT (\e -> ptp (runReaderT r1 e) iso (runReaderT r2 e))

$(defineIsomorphisms ''Atom)

infixr 6 <&>

(<&>) :: Syntax delta => delta (State a) -> delta (State b) -> delta (State (a,b))
a <&> b =  mergeState <$> a <*> b

mergeState :: Iso (State a,State b) (State (a,b)) --((Atom,Atom),[Atoms])
mergeState = Iso f g where
    f ((a1,s1),(a2,s2)) = Just ((a1,a2),s1++s2)
    g ((a1,a2),s)       = Just ((a1,s) ,(a2,s))

optState :: Iso (Maybe (State a)) (State (Maybe a))
optState = Iso f g where
    f (Just (a,as)) = Just (Just a, as)
    f Nothing       = Just (Nothing, [])
    g (Nothing,_)   = Just  Nothing
    g (Just a ,as)  = Just (Just (a,as))

stateMany :: (Eq alpha,Syntax delta) => delta (State alpha)
                                     -> delta (State [alpha])
stateMany p = (first cons <$> p <&> stateMany p) <|> pure ([],[])

stateMany1 :: (Eq alpha,Syntax delta) => delta (State alpha)
                                      -> delta (State [alpha])
stateMany1 p = first cons <$> p <&> stateMany p

stateList :: Iso [State a] (State [a])
stateList = foldl ff . init
    where ff = Iso (Just . f) (Just . g)
          f ((a,xs),(b,ys)) = (b:a,xs++ys)
          g (b:a,xs) = ((a,xs),(b,xs))
          init = Iso (\ls -> Just (([],[]),ls))
                     (\(_,ls) -> Just ls)

collapsState :: Iso (State (State a)) (State a)
collapsState = Iso (Just . f) (Just . g) where
    f ((a,ys),xs) = (a,xs++ys)
    g (a,xs) = ((a,xs),xs)

filterState :: Iso (State Sumti) (State Sumti)
filterState = Iso f g where
    f           = apply id
    g ((a,t),s) = Just ((a,t),getDefinitons [a] s)

getDefinitons :: [Atom] -> [Atom] -> [Atom]
getDefinitons ns ls = if ns == nns then links else getDefinitons nns ls
    where links = filter ff ls
          nodes = concatMap atomToList links
          nns   = nub $ ns ++ nodes
          ff l = any (`atomElem` l) ns

------------------------------------------------------------------------
letter, digit :: Syntax delta => delta Char
letter  =  subset isLetter <$> token
digit   =  subset isDigit <$> token

word :: Syntax delta => delta String
word = many1 letter <* optSpace

--any :: Syntax delta => delta String
--any = many token

--Handling for simple Strings
string :: Syntax delta => String -> delta String
string [] =  pure [] <* optext " "
string (x:xs) = cons <$> (subset (== x) <$> token) <*> string xs

mytext :: Syntax delta => String -> delta ()
mytext s = text s <* optext " "

--For text that is both optional and should be parsed into ()
optext :: Syntax delta => String -> delta ()
optext t = (text t <|> text "") <* optSpace --(optext (t++" ") <|> text t <|> text "")

--Handles 1 of many options from a list
oneOf :: Syntax delta => (a -> delta b) -> [a] -> delta b
oneOf f [e] = f e
oneOf f (x:xs) = f x <|> oneOf f xs

selmaho :: String -> SyntaxReader String
selmaho s = ReaderT (\(cmavo,_,_) -> oneOf string $ cmavo M.! s)

sepSelmaho :: String -> SyntaxReader ()
sepSelmaho s = ReaderT (\(cmavo,_,_) -> oneOf mytext $ cmavo M.! s)

optSelmaho :: String -> SyntaxReader ()
optSelmaho s = ReaderT (\(cmavo,_,_) -> oneOf optext $ cmavo M.! s)

-------------------------------------

_UI :: SyntaxReader (State Atom)
_UI = selmaho "UI"

gismu :: SyntaxReader (Atom,[Atom])
gismu = implicationOf 0 . reorder0 . node <$> pure "PredicateNode"
                                          <*> gismu_
                                          <*> pure lowTv
    where gismu_ = ReaderT (\(_,gismus,_) -> oneOf string gismus)

--Handles addtional arguments in a leP
beP :: SyntaxReader ([Sumti],[Atom])
beP = first merge <$> mytext "be" *> sumtiP <&> stateMany (mytext "bei" *> sumtiP) <* optSelmaho "BEhO"
    where merge = Iso (\(a,b) -> Just (a:b)) (\(x:xs) -> Just (x,xs))

pureVarNode :: SyntaxReader (Sumti,[Atom])
pureVarNode = pure ((Node "VariableNode" "$var" noTv,Nothing),[])

--Handles anykind of LE phrases
-- State (s,(v,[a]))
--TODO: consdier distinctions of defferent words in LE
leP :: SyntaxReader (Atom,[Atom])
leP = first (_ssl . second handleBE) <$> sepSelmaho "LE"
                                      *> selbri
                                     <&> pureVarNode
                                     <&> (optState <$> optional beP)
                                     <* optSelmaho "KU"

-- ((Pred,S),[Args]) -> ((pred,[args]),S)
-- ((Pred,S),([Args],Maybe [(Arg,S2)]) -> ((pred,[args]),S)

handleBE :: Iso (Sumti,Maybe [Sumti]) [Sumti]
handleBE = Iso (\(a,mas) -> case mas of
                               Just as -> Just $ a:as
                               Nothing -> Just [a])
               (\(a:as)  -> if as == []
                               then Just (a,Nothing)
                               else Just (a,Just as))

--Handle anykind of LA phrase
laP :: SyntaxReader (Atom,[Atom])
laP = handleName . node <$> sepSelmaho "LA" *> pure "ConceptNode" <*> word <*> pure lowTv  <* optSelmaho "KU"

handleName :: Iso Atom (Atom,[Atom])
handleName = Iso (\a -> let c = cCN "rand" lowTv
                            p = cPN "cmene" lowTv
                            l = cEvalL highTv p (cLL [a,c])
                        in Just (c,[l]))
                 (\(_,[EvalL _ (LL [a,_])]) -> Just a)

liP :: SyntaxReader (Atom,[Atom])
liP = sepSelmaho "LI" *> (xo <|> paP) <* optSelmaho "LOhO"

paP :: SyntaxReader (Atom,[Atom])
paP =  reorder0 . node <$> pure "NumberNode"
    <*> (intToString <$> pa)
    <*> pure lowTv

pa :: SyntaxReader Int
pa = paToNum <$> many1 (selmaho "PA")

xo :: SyntaxReader (Atom,[Atom])
xo = reorder0 . node <$> pure "VariableNode"
    <*> string "xo"
    <*> pure lowTv

intToString :: (Read a, Show a) => Iso a String
intToString = Iso (Just . show) (Just . read)

paToNum :: Iso [String] Int
paToNum = foldl ff . first (inverse $ ignore 0) . commute . unit

ff :: Iso (Int,String) Int
ff = splitLastDigit . second _paToNum

splitLastDigit :: Iso (Int,Int) Int
splitLastDigit = Iso f g where
    f (i,j) = Just (i*10+j)
    g 0     = Nothing
    g n     = Just (n `div` 10,n `mod` 10)

_paToNum :: Iso String Int
_paToNum = mkSynonymIso numSynonyms
    where numSynonyms = [("no",0),("pa",1),("re",2),("ci",3),("vo",4)
                        ,("mu",5),("xa",6),("ze",7),("bi",8),("so",9)]

mkSynonymIso :: (Eq a, Eq b) => [(a,b)] -> Iso a b
mkSynonymIso ls = Iso f g where
    f e = snd P.<$> F.find (\(a,b) -> a == e) ls
    g e = fst P.<$> F.find (\(a,b) -> b == e) ls

--Handels all pronouns
kohaP1 :: SyntaxReader (Atom,[Atom])
kohaP1 = reorder0 . node <$> pure "ConceptNode"
                         <*> selmaho "KOhA"
                         <*> pure lowTv

--Special case for the prounoun ma
--It is a fill the blank question so needs to be a Variable Node
ma :: Syntax delta => delta (Atom,[Atom])
ma = reorder0 . node <$> pure "VariableNode" <*> string "ma" <*> pure noTv

--KohaPharse for any kind of Pro-Noune
kohaP :: SyntaxReader (Atom,[Atom])
kohaP = ma <|> kohaP1

--This Handles relative phrases
noiP :: SyntaxReader (Atom,[Atom])
noiP = sepSelmaho "NOI" *> bridi <* optSelmaho "KUhO"

goiP :: SyntaxReader (Atom,[Atom])
goiP = ptp (selmaho "GOI") goiToNoi noiP

goiToNoi :: Iso String String
goiToNoi = mkSynonymIso goinoi
    where goinoi = [("pe","poi ke'a srana")
                   ,("po","poi ke'a se steci srana")
                   ,("po'e","poi jinzi ke se steci srana")
                   ,("po'u","poi du")
                   ,("ne","noi ke'a srana")
                   ,("no'u","noi du")]

--This handles unconected sumti with optional relative phrases
sumti :: SyntaxReader (Atom,[Atom])
sumti =  ((kehaToSesku . handleNOI) ||| id) . ifJustB
      <$> (kohaP <|> leP <|> laP <|> liP) <*> optional2 (noiP <|> goiP)
    where handleNOI = Iso (\((a,b),(c,d)) -> Just (a,c:d++b))
                          (\(a,c:b) -> Just ((a,b),(c,b)))

--If we have a relative clause
--this will switch the ke'a with the actually concept
kehaToSesku :: Iso (State Atom) (State Atom)
kehaToSesku = Iso (\(c,l) -> let nl = map (f kea c) l
                             in if nl == l
                                 then Just (c,nl)
                                 else Nothing)
                  (\(c,l) -> let nl = map (f c kea) l
                             in if nl == l
                                 then Just (c,nl)
                                 else Nothing)
    where kea = Node "ConceptNode" "ke'a" lowTv
          f a b l@(Link "InheritanceLink" [x,c] tv)
            | c == a = Link "InheritanceLink" [x,b] tv
            | otherwise = l
          f _ _ l = l

-- (State,Maybe State) -> Either (State,State) (State)
-- ((Atom,[Atom]),Atom) -> State -> State

--This Handels Sumti connected by logical connectives
sumtiC :: SyntaxReader (State Atom)
sumtiC = ((first conLink . handleLojjohe) ||| id) . ifJustB <$> sumti <*> optional (selmaho "A" <*> sumtiC)
    where handleLojjohe = Iso (\((a1,s1),(con,(a2,s2))) -> Just ((con,[a1,a2]),s1++s2))
                              (\((con,[a1,a2]),s) -> Just ((a1,s),(con,(a2,s))))

sumtiP :: SyntaxReader (State Sumti)
sumtiP =  handleFA  <$> optional (selmaho "FA") <*> sumtiC
    where handleFA = first commute . associate . first (isofmap faToPlace)

faToPlace :: Iso String String
faToPlace = mkSynonymIso [("fa","1")
                         ,("fe","2")
                         ,("fi","3")
                         ,("fo","4")
                         ,("fu","5")]

fihoP :: SyntaxReader (State (Tagged Selbri))
fihoP = sepSelmaho "FIhO" *> selbri <* optSelmaho "FEhU"

baiP :: SyntaxReader (State (Tagged Selbri))
baiP = ReaderT (\wl@(_,_,btf) -> runReaderT (_bai btf) wl)
    where _bai btf = ptp (selmaho "BAI") (mkSynonymIso btf) selbri

modalSumti :: SyntaxReader (State Sumti)
modalSumti = reorder . first handleFIhO <$> (fihoP <|> baiP)
                                        <&> sumtiP --TODO maybe use sumtiC and init Empty Tag
    where handleFIhO = (fi'otag &&& _frame) . second (inverse tolist1)
                                            . handleTAG . second tolist1
          fi'otag = Iso (Just . f) (Just . g)
          f ((tv,PN name),(s,Just tag)) = (s,Just $ name++tag++tv)
          g (s,Just nametag) = let [name,tag,tv] = S.split (S.oneOf "12345") nametag
                               in ((tv,cPN name lowTv),(s,Just tag))
          reorder = Iso (\((a,b),c) -> Just (a,b: c))
                        (\ (a,b: c) -> Just ((a,b),c))


quantifiedSumti :: SyntaxReader (State Sumti)
quantifiedSumti = (ptp (pa <*> selbri) id (ptp pa addLE _quantifiedSumti))
                  <|> _quantifiedSumti
    where addLE = Iso (Just . f) (Just . g)
          f s = s ++ " lo "
          g s = take (length s - 4) s



--(Maybe pa,(Atom,Tag))
--State (State Atom,Tag)
_quantifiedSumti :: SyntaxReader (State Sumti)
_quantifiedSumti = reorder
                . first ((handleQ ||| handleNQ) . ifJustA)
                <$> opPa
                <&> sumtiAll

    where handleQ = first (first andl . stateList . isoTake . second extraInstance) . associate
          handleNQ = first (instanceOf 0 . reorder0)
          opPa = optState <$> optional (reorder0 <$> pa)
          reorder = Iso f g
          f (((a,s1),t),s2) = Just ((a,t),s1++s2)
          g ((a,t),s)       = Just (((a,s),t),s)

isoTake :: Iso (Int,[a]) [a]
isoTake = Iso f g where
    f (i,ls) = Just $ take i ls
    g ls = Just (length ls,ls)

extraInstance :: Iso Atom [State Atom]
extraInstance = Iso f g where
    f a = Just $ map (\x -> fromJust $ apply (instanceOf x . reorder0) a) [0..]
    g [] = error "Should never be empty"
    g (a:_) = unapply (instanceOf 0 . reorder0) a

sumtiAll :: SyntaxReader (State Sumti)
sumtiAll = filterState <$> modalSumti <|> sumtiP

nuP :: SyntaxReader (Atom,[Atom])
nuP = handleNU <$> sepSelmaho "NU" *> withText bridi <* optSelmaho "KEI"

handleNU :: Iso ((Atom,[Atom]),String) (Atom,[Atom])
handleNU = Iso f g where
    f ((atom,as),name) = let pred = cPN name lowTv
                             link = mkCtxPre pred atom
                         in Just (pred,link:as)
    g (PN name,CtxPred atom : as) = Just ((atom,as),name)
    g _ = Nothing

_NAhE :: SyntaxReader (State String)
_NAhE = reorder0 <$> (selmaho "NAhE" <|> pure "")

_selbri :: SyntaxReader (State (Tagged Atom))
_selbri = filterState . first commute . associate <$> optional2 (selmaho "SE")
                                                  <*> (gismu <|> nuP)
selbri :: SyntaxReader (State (Tagged Selbri))
selbri = first associate <$> _NAhE <&> _selbri

_PU :: SyntaxReader (State Atom)
_PU = reorder0 . concept <$> selmaho "PU"

_ZI :: SyntaxReader (State Atom)
_ZI = reorder0 . concept <$> selmaho "ZI"

_trati :: SyntaxReader (State (Maybe Atom))
_trati = first handleTrati <$> stateMany (_PU <|> _ZI)
    where handleTrati = Iso (Just . f) (Just . g)
          f [] = Nothing
          f xs = apply andl xs
          g Nothing   = []
          g (Just xs) = fromJust $ unapply andl xs

_NA :: SyntaxReader (State String)
_NA = reorder0 <$> selmaho "NA"

naheToTV :: Iso String TruthVal
naheToTV = mkSynonymIso [("je'a",stv 1    0.9)
                        ,(""    ,stv 0.75 0.9)
                        ,("no'e",stv 0.5  0.9)
                        ,("na'e",stv 0.25 0.9)
                        ,("to'e",stv 0    0.9)]

--THis Handles compelte sentences
-- Remark: Handle the modal Sumti before handleBRIDI
bridi :: SyntaxReader (Atom,[Atom])
bridi = handleBRIDI . first mergeSumti <$> stateMany1 quantifiedSumti
                                       <*   optext "cu"
                                       <&> _trati
                                       <&> (optState <$> optional2 _NA)
                                       <&> selbri
                                       <&> stateMany quantifiedSumti

partitionIso :: (a -> Bool) -> Iso [a] ([a],[a])
partitionIso p = Iso f g where
    f ls = Just $ partition p ls
    g (xs,ys) = Just $ xs ++ ys


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


preti :: SyntaxReader Atom
preti = ((_satl . associate) ||| handleMa) . ifJustA <$> optional (string "xu") <*> bridi
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



--Arrow Helpers

second a = id *** a
first  a = a *** id

--For dealing with maybes from/for Optional in the first or second position
ifJustA :: Iso (Maybe a,b) (Either (a,b) b)
ifJustA = Iso (\case {(Just a,b) -> Just $ Left (a,b) ; (Nothing,b) -> Just $  Right b})
              (\case {Left (a,b) -> Just (Just a,b) ;  Right b  -> Just (Nothing,b)})

ifJustB :: Iso (a,Maybe b) (Either (a,b) a)
ifJustB = Iso (\case {(a,Just b) -> Just $ Left (a,b) ; (a,Nothing) -> Just $  Right a})
              (\case {Left (a,b) -> Just (a,Just b) ;  Right a  -> Just (a,Nothing)})

--For converting elements or tuples into lists
--Lists are needed as arguments to form Link Atoms
tolist1 :: Iso a [a]
tolist1 = Iso (\a -> Just [a]) (\[a] -> Just a)

tolist2 :: Show a => Iso (a,a) [a]
tolist2 = Iso (\(a1,a2) -> Just [a1,a2])
              (\case {[a1,a2] -> Just (a1,a2); a -> error $ "tolist2: " ++ show a})

--Atom Helpers

--Many of the Iso take/result in (Atom,[Atom])
--The following reorder functions merge the list of Atoms into 1
--And creates a tuple with all the single Atoms in the first element of the tuple
reorder0 :: Iso a (State a)
reorder0 = Iso (\a -> Just (a,[]))
               (\(a,_) -> Just a)

--Most pronouns are instances of a more general concept
--This will create the inheritance link to show this relation
instanceOf :: Int -> Iso (State Atom) (State Atom)
instanceOf = genInstance "InheritanceLink"

implicationOf :: Int -> Iso (State Atom) (State Atom)
implicationOf = genInstance "ImplicationLink"

genInstance :: String -> Int -> Iso (State Atom) (State Atom)
genInstance typeL num = Iso f g where
    f (e@(Node typeS _ _),s) = let i = Node typeS ("rand"++ show e ++ show num) noTv
                                   l = Link typeL [i,e] highTv
                               in Just (i,l:s)
    f (e,s) = let i = Node "ConceptNode" ("rand"++ show e ++ show num) noTv
                  l = Link typeL [i,e] highTv
              in Just (i,l:s)
    g (n,ls) =  (\(Link _ [_,i] _) -> (i,ls)) `fmap` F.find (ff n) ls
    ff n (Link "InheritanceLink" [b,_] _) = n == b
    ff n a = False

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

isoZip :: Iso ([a],[b]) [(a,b)]
isoZip = Iso (Just . uncurry zip) (Just . unzip)

mapIso :: Iso a b -> Iso [a] [b]
mapIso iso = Iso f g where
    f = mapM $ apply iso
    g = mapM $ unapply iso

_frames :: Iso (Tagged Selbri,[Sumti]) Atom
_frames = andl . mapIso _frame . isoZip . reorder . handleTAG
    where reorder = Iso f g
          f (a,b)     = Just (replicate (length b) a,b)
          g (a:_,b) = Just (a,b)

handleTAG :: Iso (Tagged Selbri,[Sumti]) (Selbri,[Sumti])
handleTAG = handleTAGupdater . second tagger
    where handleTAGupdater = Iso (Just . f) (Just . g)
          f ((s,Nothing),args) = (s,args)
          f ((s,Just u) ,args) = (s,map (mapf u) args)
          g (s,args)           = ((s,Nothing),args)
          mapf u = mapSnd $ (=<<) $ apply (tagUpdater u)

tagUpdater :: String -> Iso Tag Tag
tagUpdater "se" = mkSynonymIso [("1","2"),("2","1")]
tagUpdater "te" = mkSynonymIso [("1","3"),("3","1")]
tagUpdater "ve" = mkSynonymIso [("1","4"),("4","1")]
tagUpdater "xe" = mkSynonymIso [("1","5"),("5","1")]

--Get the argumetn location of all Sumties
tagger :: Iso [(Atom,Maybe String)] [(Atom,Maybe String)]
tagger = post . foldl tagOne . init
    where init = Iso (\a     -> Just (([],("0",startMap)),a))
                     (\(_,a) -> Just a)
          startMap = M.fromList [("1",True),("2",True),("3",True),("4",True),("5",True)]
          post = Iso (\(l,(_,_)) -> Just l)
                     (\l         -> Just (l,(show $ length l,M.empty)))
          tagOne = Iso (Just . f) (Just . g)
          f ((r,(p,u)),(a,Just s))
            | length s >  1 = ((a,Just s):r,(p,u))
            | length s == 1 = ((a,Just s):r,(s,M.update (\_ -> Just False) s u))
          f ((r,(p,u)),(a,Nothing)) =
                              ((a,Just t):r,(t,M.update (\_ -> Just False) t u))
                where next s = show (read s + 1)
                      t = findNext p
                      findNext s = let t = next s
                                   in if u M.! t then t else findNext t
          g ((a,Just s):r,(p,u))
            | length s >  1 = ((r,(p     ,u)), (a,Just s ))
            | s == p        = ((r,(prev p,u)), (a,Nothing))
            | otherwise     = ((r,(prev p,u)), (a,Just s ))
                where prev s = show (read s - 1 )

--        Iso       Selbri          Stumti       Atom
_frame :: Iso ((String,Atom),(Atom,Maybe Tag)) Atom
_frame = _evalTv . (naheToTV *** (_framePred *** tolist2)) . reorder
    where reorder = Iso f g
          f ((tv,s),(a,Just t)) = Just (tv,((s,t),(s,a)))
          g (tv,((s,t),(_,a)))  = Just ((tv,s),(a,Just t))

_framePred :: Iso (Atom,Tag) Atom
_framePred = predicate . toName "_sumti". tolist2 . first (inverse predicate)

toName :: String -> Iso [String] String
toName x = Iso (Just . intercalate x) (Just . S.splitOn x)

--Various semi-isos to easily transfrom Certain Atom types

_eval :: Iso (Atom,[Atom]) Atom
_eval = eval . tolist2 . second list

_evalTv :: Iso (TruthVal,(Atom,[Atom])) Atom
_evalTv = evalTv . second (tolist2 . second list)

_ctx :: Iso (Maybe Atom,Atom) Atom
_ctx = ((ctx . tolist2) ||| id) . ifJustA

_ctxold :: Iso (Atom,(Atom,[Atom])) Atom
_ctxold = ctx . tolist2 . second _eval

_ssl :: Iso (Tagged Selbri,[Sumti]) Atom
_ssl = ssl . tolist2 . addVarNode . _frames

addVarNode :: Iso Atom (Atom,Atom)
addVarNode = Iso (\a -> Just (Node "VariableNode" "$var" noTv,a))
                 (\(_,a) -> Just a)

_satl :: Iso ((String,Atom),[Atom]) Atom
_satl = Iso (\((_,a),s) -> let all = Link "ListLink" (a:s) noTv
                           in Just $ Link "SatisfactionLink" [all] noTv)
            (\case {(Link "SatisfactionLink" (a:s) _) -> Just (("xu",a),s)
                   ;_ -> Nothing})

ctx :: Iso [Atom] Atom
ctx = linkIso "ContextLink" noTv

eval :: Iso [Atom] Atom
eval = linkIso "EvaluationLink" noTv

evalTv :: Iso (TruthVal,[Atom]) Atom
evalTv = linkIso2 "EvaluationLink"

ssl :: Iso [Atom] Atom
ssl = linkIso "SatisfyingSetLink" noTv

list :: Iso [Atom] Atom
list = linkIso "ListLink" noTv

andl :: Iso [Atom] Atom
andl = linkIso "AndLink" noTv

conLink :: Iso (String,[Atom]) Atom
conLink = Iso (\(s,args) -> case s of
                             "e" -> apply link ("AndLink",(args,noTv))
                             "a" -> apply link ("OrLink",(args,noTv)))
              (\a -> case unapply link a of
                        Just ("AndLink",(args,_)) -> Just ("e",args)
                        Just ("OrLink",(args,_))  -> Just ("a",args)
                        e -> Nothing)

linkIso :: String -> TruthVal -> Iso [Atom] Atom
linkIso n t = link . Iso (\l -> Just (n,(l,t)))
                         (\(an,(l,at)) -> if an == n
                                           then Just l
                                           else Nothing)

linkIso2 :: String -> Iso (TruthVal,[Atom]) Atom
linkIso2 n = link . Iso (\(t,l) -> Just (n,(l,t)))
                        (\(an,(l,t)) -> if an == n
                                          then Just (t,l)
                                          else Nothing)

nodeIso :: String -> TruthVal -> Iso String Atom
nodeIso n t = node . Iso (\l -> Just (n,(l,t)))
                         (\(an,(l,at)) -> if an == n
                                           then Just l
                                           else Nothing)
concept :: Iso String Atom
concept = nodeIso "ConceptNode" noTv

predicate :: Iso String Atom
predicate = nodeIso "PredicateNode" noTv

variable :: Iso String Atom
variable = nodeIso "VariableNode" noTv --is this even usefull?
