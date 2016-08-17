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
import Data.List (partition,isPrefixOf)
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

type WordList = (M.Map String [String],[String])
type MyReader a = forall delta. Syntax delta => ReaderT WordList delta a

instance IsoFunctor f => IsoFunctor (ReaderT a f) where
    iso <$> r
        = ReaderT (\e -> iso <$> runReaderT r e)

instance ProductFunctor f => ProductFunctor (ReaderT a f) where
    a <*> b
        = ReaderT (\e -> runReaderT a e <*> runReaderT b e)

instance Alternative f => Alternative (ReaderT a f) where
    a <|> b
        = ReaderT (\e -> runReaderT a e <|> runReaderT b e)
    empty = ReaderT (\e -> empty)

instance Syntax f => Syntax (ReaderT a f) where
    pure x = ReaderT (\e -> pure x)
    token  = ReaderT (\e -> token)
    withText r = ReaderT (\e -> withText $ runReaderT r e)

$(defineIsomorphisms ''Atom)

letter, digit :: Syntax delta => delta Char
letter  =  subset isLetter <$> token
digit   =  subset isDigit <$> token

word :: Syntax delta => delta String
word = many1 letter <* optSpace

any :: Syntax delta => delta String
any = many token

--Handling for simple Strings
string :: Syntax delta => String -> delta String
string [] = nil <$> pure () <* optext " "
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

selmaho :: String -> MyReader String
selmaho s = ReaderT (\(cmavo,_) -> oneOf string $ cmavo M.! s)

sepSelmaho :: String -> MyReader ()
sepSelmaho s = ReaderT (\(cmavo,_) -> oneOf mytext $ cmavo M.! s)

optSelmaho :: String -> MyReader ()
optSelmaho s = ReaderT (\(cmavo,_) -> oneOf optext $ cmavo M.! s)

gismu :: MyReader (Atom,[Atom])
gismu = reorder0 . node <$> pure "PredicateNode" <*> gismu_ <*> pure noTv
    where gismu_ = ReaderT (\(_,gismus) -> oneOf string gismus)

--Handles addtional arguments in a leP
beP :: MyReader [(Atom,[Atom])]
beP = merge <$> mytext "be" *> sumtiP <*> many (mytext "bei" *> sumtiP) <* optSelmaho "BEhO"
    where merge = Iso (\(a,b) -> Just (a:b)) (\(x:xs) -> Just (x,xs))

--((Atom,[Atom]),[(Atom,[Atom])])

--Handles anykind of LE phrases
leP :: MyReader (Atom,[Atom])
leP = instanceOf . first _ssl . handleBE <$> sepSelmaho "LE" *> selbri <*> pure (Node "VariableNode" "$var" noTv) <*> optional beP <* optSelmaho "KU"

-- ((Pred,S),[Args]) -> ((pred,[args]),S)
-- ((Pred,S),([Args],Maybe [(Arg,S2)]) -> ((pred,[args]),S)

handleBE :: Iso (AtomState,(Atom,Maybe [AtomState])) ((Atom,[Atom]),[Atom])
handleBE = Iso (\((p,s1),(a1,mas1)) -> case mas1 of
                                        Just as1 -> let a = map fst as1
                                                        s = map snd as1
                                                    in Just ((p,a1:a),concat (s1:s))
                                        Nothing -> Just ((p,[a1]),s1))
               (\((p,a1:a),s) -> Just ((p,s),(a1,listToMaybe $ map (\e -> (e,s)) a)))
    where listToMaybe [] = Nothing
          listToMaybe a = Just a

--Handle anykind of LA phrase
laP :: MyReader (Atom,[Atom])
laP = instanceOf . handleName . node <$> sepSelmaho "LA" *> pure "ConceptNode" <*> word <*> pure lowTv  <* optSelmaho "KU"

handleName :: Iso Atom (Atom,[Atom])
handleName = Iso (\a -> let c = cCN "rand" lowTv
                            p = cPN "cmene" lowTv
                            l = cEvalL highTv p (cLL [a,c])
                        in Just (c,[l]))
                 (\(_,[EvalL _ (LL [a,_])]) -> Just a)

liP :: MyReader (Atom,[Atom])
liP = sepSelmaho "LI" *> paP <* optSelmaho "LOhO"

paP :: MyReader (Atom,[Atom])
paP =  reorder0 . node <$> pure "NumberNode"
    <*> (intToString . paToNum <$> many1 (selmaho "PA"))
    <*> pure lowTv

intToString :: (Read a, Show a) => Iso a String
intToString = Iso (\a -> Just $ show a) (\a -> Just $ read a) where

paToNum :: Iso [String] Int
paToNum = foldl ff . (first $ inverse $ ignore 0) . commute . unit

ff :: Iso (Int,String) Int
ff = splitLastDigit . second _paToNum

splitLastDigit :: Iso (Int,Int) Int
splitLastDigit = Iso f g where
    f (i,j) = Just (i*10+j)
    g n     = Just (n `div` 10,n `mod` 10)

_paToNum :: Iso String Int
_paToNum = mkSynonymIso numSynonyms
    where numSynonyms = [("no",0),("pa",1),("re",2),("ci",3),("vo",4)
                        ,("mu",5),("xa",6),("ze",7),("bi",8),("so",9)]

goiToNoi :: Iso String String
goiToNoi = mkSynonymIso goinoi
    where goinoi = [("pe","poi ke'a srana")
                   ,("po","poi ke'a se steci srana")
                   ,("po'e","poi jinzi ke se steci srana")
                   ,("po'u","poi du")
                   ,("ne","noi ke'a srana")
                   ,("no'u","noi du")]
{-Iso f g where
    f "no" = Just 0
f "pa" = Just 1
f "re" = Just 2
f "ci" = Just 3
f "vo" = Just 4
f "mu" = Just 5
f "xa" = Just 6
f "ze" = Just 7
f "bi" = Just 8
f "so" = Just 9
g 0 = Just "no"
g 1 = Just "pa"
g 2 = Just "re"
g 3 = Just "ci"
g 4 = Just "vo"
g 5 = Just "mu"
g 6 = Just "xa"
g 7 = Just "ze"
g 8 = Just "bi"
g 9 = Just "so"
-}

mkSynonymIso :: [(a,b)] -> Iso a b
mkSynonymIso ls = Iso f g where
    f e = snd P.<$> find (\(a,b) -> a == e) ls
    f e = fst P.<$> find (\(a,b) -> b == e) ls

--Handels all pronouns
kohaP1 :: MyReader (Atom,[Atom])
kohaP1 = instanceOf . reorder0 . node <$> pure "ConceptNode"
                                      <*> selmaho "KOhA"
                                      <*> pure lowTv

--Special case for the prounoun ma
--It is a fill the blank question so needs to be a Variable Node
ma :: Syntax delta => delta (Atom,[Atom])
ma = varInstance . reorder0 . node <$> pure "VariableNode" <*> (string "ma") <*> pure noTv

--KohaPharse for any kind of Pro-Noune
kohaP :: MyReader (Atom,[Atom])
kohaP = ma <|> kohaP1

--This Handles relative phrases
noiP :: MyReader (Atom,[Atom])
noiP = sepSelmaho "NOI" *> bridi <* optSelmaho "KUhO"

--This handles unconected sumti with optional relative phrases
sumti :: MyReader (Atom,[Atom])
sumti =  ((kehaToSesku . handelNOI) ||| id) . ifJustB
      <$> (kohaP <|> leP <|> laP <|> liP) <*> optional noiP
    where handelNOI = Iso (\((a,b),(c,d)) -> Just (a,c:d++b))
                          (\(a,c:b) -> Just ((a,b),(c,b)))

-- (State,Maybe State) -> Either (State,State) (State)
-- ((Atom,[Atom]),Atom) -> State -> State

--This Handels Sumti connected by logical connectives
sumtiP :: MyReader (Atom,[Atom])
sumtiP = ((first conLink . handleLojjohe) ||| id) . ifJustB <$> sumti <*> optional (selmaho "A" <*> sumtiP)
    where handleLojjohe = Iso (\((a1,s1),(con,(a2,s2))) -> Just ((con,[a1,a2]),s1++s2))
                              (\((con,[a1,a2]),s) -> Just ((a1,s),(con,(a2,s))))

--(State,Maybe (String,State)) -> (Either (State) (State,(String,State))
--(State,(String,State) -> ((String,[Atom]),[Atom]) -> (State)

--selbri :: MyReader ((Maybe String,Atom),[Atom])
--selbri = reorder0 <$> optional (selmaho "SE") <*> selbriNode
--    where selbriNode = node <$> pure "PredicateNode" <*> gismu <*> pure noTv

nuP :: MyReader (Atom,[Atom])
nuP = handleNU <$> sepSelmaho "NU" *> withText bridi <* optSelmaho "KEI"

handleNU :: Iso ((Atom,[Atom]),String) (Atom,[Atom])
handleNU = Iso (\((atom,as),name) -> let pred = cPN name lowTv
                                         link = mkCtxPre pred atom
                                     in Just (pred,link:as))
               (\(PN name,(CtxPred atom):as) -> Just ((atom,as),name))

selbri :: MyReader (Atom,[Atom])
selbri = handleSE <$> optional (selmaho "SE") <*> (gismu <|> nuP)

handleSE :: Iso (Maybe String,(Atom,[Atom])) (Atom,[Atom])
handleSE = Iso f g where
    f (m,(a@(PN name),as)) =
                    case m of
                        Nothing -> Just (a,as)
                        Just se ->
                            let link = equSE name se
                                seName = se ++ name
                            in Just (cPN seName lowTv,link:as)
    g (a@(PN seName),head:as) =
                    case isSE seName of
                        False -> Just (Nothing,(a,head:as))
                        True  ->
                            let name = drop 2 seName
                                se   = take 2 seName
                            in Just (Just se,(cPN name lowTv,as))
    isSE name = foldr (\e b -> b || isPrefixOf e name) False ["se","te","ve","xe"]

equSE pred se =
    Link "EquivalenceLink"
        [ cLamdaL noTv varList
            (cEvalL highTv (cPN pred        lowTv) (varList))
        , cLamdaL noTv varList
            (cEvalL highTv (cPN (se++pred)  lowTv) (seList se))
        ] highTv
    where varList = createVarList 5
          seList "se" = cVL [cVN "2",cVN "1",cVN "3",cVN "4",cVN "5"]
          seList "te" = cVL [cVN "3",cVN "2",cVN "1",cVN "4",cVN "5"]
          seList "ve" = cVL [cVN "4",cVN "2",cVN "3",cVN "1",cVN "5"]
          seList "xe" = cVL [cVN "5",cVN "2",cVN "3",cVN "4",cVN "1"]

createVarList n = cVL $ varNodes 1
    where varNodes i | i == n     = [cVN (show n)]
                     | otherwise  = cVN (show i) : varNodes (i+1)


_PU :: MyReader (Atom,[Atom])
_PU = reorder0 . node <$> pure "ConceptNode" <*> selmaho "PU" <*> pure noTv

_NA :: MyReader (String,[Atom])
_NA = reorder0 <$> selmaho "NA"

--THis Handles compelte sentences
bridi :: MyReader (Atom,[Atom])
--bridi =
--  ((first _ctx . reorder2) ||| (first _eval . reorder1)) . ifJustA . handleSumti
--  <$> many1 sumtiP <*> optional tense <*> selbri <*> many sumtiP
bridi = handleBRIDI . first mergeSumti <$> (getSumti <$> many1 sumtiP)
                                       <&> (optState <$> optional _PU)
                                       <&> (optState <$> optional _NA)
                                       <&> selbri
                                       <&> (getSumti <$> many sumtiP)


infixr 6 <&>

(<&>) :: MyReader (State a) -> MyReader (State b) -> MyReader (State (a,b))
a <&> b =  mergeState <$> a <*> b

optState :: Iso (Maybe (State a)) (State (Maybe a))
optState = Iso f g where
    f (Just (a,as)) = Just (Just a, as)
    f Nothing       = Just (Nothing, [])
    g (Nothing,_)   = Just  Nothing
    g (Just a ,as)  = Just (Just (a,as))

-- (a,(mp,(ma,(s,aa))))
-- (mp,(ma,(s,a++aa)))
-- ((mp,(ma,(s,a))),as)
-- (bridi,as)

handleBRIDI :: Iso ((Maybe Atom,(Maybe String,(Atom,[Atom]))),[Atom]) (Atom,[Atom])
handleBRIDI = first $ handleNA . second _ctx . inverse associate . first commute . second _eval . associate

-- ((MPU,(MNA,(Selbri,Args)))   ,Atoms)
-- (((MPU,MNA),(Selbri,Args))   ,Atoms)
-- (((MPU,MNA),Eval)            ,Atoms)
-- (((MNA,MPU),Eval)            ,Atoms)
-- ((MNA,(MPU,Eval))            ,Atoms)
-- ((MNA,MCtxL)                 ,Atoms)
-- (bridi                       ,Atoms)

handleNA :: Iso (Maybe String,Atom) (Atom)
handleNA = Iso f g where
    f (Nothing,a)    = Just a
    f (Just n, a)    = apply _eval ((cGPN n lowTv),[a])
    g (EvalL (GPN n) a) = Just (Just n,a)

--For mergin sumties before and after the selbri into a single list
mergeSumti :: (a ~ aa) => Iso ([a],(pu,(na,(s,[aa])))) (pu,(na,(s,[a])))
mergeSumti = Iso f g where
    f (a1,(pu,(na,(s,a2)))) = Just (pu,(na,(s,a1++a2)))
    g     (pu,(na,(s,a)))   = case a of
                                   [] -> Nothing
                                   (x:xs) -> Just ([x],(pu,(na,(s,xs))))

preti :: MyReader Atom
preti = ((_satl . associate) ||| handleMa) . ifJustA <$> optional (string "xu") <*> bridi
    where handleMa =
              Iso (\(a,s) ->
                    let x = atomFold (\r a -> r || isMa a) False a
                        isMa (Node "VariableNode" x noTv) = not $ x == "$var"
                        isMa _ = False
                        all = Link "ListLink" (a:s) noTv
                        na = Link "PutLink" [all,Link "GetLink" [all] noTv] noTv
                    in Just (x ? na $ all))
                  (\(ma) -> case ma of
                      (Link "PutLink"  [LL (a:s),_] _) -> Just (a,s)
                      (Link "ListLink" (a:s) _) -> Just (a,s))

--Arrow Helpers

second a = (id *** a)
first  a = (a *** id)

--For dealing with maybes from/for Optional in the first or second position
ifJustA :: Iso (Maybe a,b) (Either (a,b) b)
ifJustA = Iso (\case {(Just a,b) -> Just $ Left (a,b) ; (Nothing,b) -> Just $  Right b})
              (\case {Left (a,b) -> Just (Just a,b) ;  Right b  -> Just (Nothing,b)})

ifJustB :: Iso (a,Maybe b) (Either (a,b) a)
ifJustB = Iso (\case {(a,Just b) -> Just $ Left (a,b) ; (a,Nothing) -> Just $  Right a})
              (\case {Left (a,b) -> Just $ (a,Just b) ;  Right a  -> Just $ (a,Nothing)})

--For converting elements or tuples into lists
--Lists are needed as arguments to form Link Atoms
tolist1 :: Iso a [a]
tolist1 = Iso (\a -> Just [a]) (\[a] -> Just a)

tolist2 :: Show a => Iso (a,a) [a]
tolist2 = Iso (\(a1,a2) -> Just [a1,a2])
              (\case {[a1,a2] -> Just (a1,a2); a -> error $ "tolist2: " ++ show a})

--Atom Helpers

--The firs element of the tuple is a Atom that is part of the main Sentence/Link
--The List are other atoms which have to be added to the Atomspace or are needed for printing
type State a = (a,[Atom])
type AtomState = (State Atom)

--Many of the Iso take/result in (Atom,[Atom])
--The following reorder functions merge the list of Atoms into 1
--And creates a tuple with all the single Atoms in the first element of the tuple
reorder0 :: Iso a (a,[Atom])
reorder0 = Iso (\a -> Just (a,[]))
               (\(a,_) -> Just a)

{-reorder1 :: Iso (State,[State]) ((Atom,[Atom]),[Atom])
reorder1 = Iso (\((a,s),ls) -> let fs = map fst ls
                                   sn = map snd ls
                               in Just ((a,fs),concat $ s:sn))
               (\((a,fs),s) -> Just ((a,s),map (\a -> (a,s))fs))

reorder2 :: Iso (State,(State,[State])) ((Atom,(Atom,[Atom])),[Atom])
reorder2 = Iso (\((a1,s1),((a2,s2),ls)) -> let fs = map fst ls
                                               sn = map snd ls
                                           in Just ((a1,(a2,fs)),concat $ s1:s2:sn))
               (\((a1,(a2,fs)),s) -> Just ((a1,s),((a2,s),map (\a -> (a,s)) fs)))
-}

mergeState :: Iso (State a,State b) (State (a,b)) --((Atom,Atom),[Atoms])
mergeState = Iso f g where
    f ((a1,s1),(a2,s2)) = Just ((a1,a2),s1++s2)
    g ((a1,a2),s)       = Just ((a1,s),(a2,s))

getSumti :: Iso [State a] (State [a])
getSumti = Iso f g where
    f ls = Just (map fst ls,concat $ map snd ls)
    g (fst,snd) = Just (zip fst $ replicate (length fst) snd)

--If we have a relative clause
--this will switch the ke'a with the actually concept
kehaToSesku :: Iso AtomState AtomState
kehaToSesku = Iso (\(c,l) -> case partition tf l of
                                ([],_) -> Nothing
                                (a,b)  -> Just (c,map (f kea c) a ++ b)
                                _ -> error "This is not implemented yet.")
                  (\(c,l) -> case partition tf l of
                                ([],_) -> Nothing
                                (a,b)  -> Just (c,map (f c kea) a ++ b)
                                _ -> error "This is not implemented yet.")
    where kea = Node "ConceptNode" "ke'a" lowTv
          f a b = atomMap (\c -> if c == a then b else c)
          tf (Link "InheritanceLink" _ _) = True
          tf a = False

--Most pronouns are instances of a more general conecpt
--This will create the inheritance link to show this relation
instanceOf :: Iso AtomState AtomState
instanceOf = genInstance "ConceptNode"

varInstance :: Iso AtomState AtomState
varInstance = genInstance "VariableNode"

genInstance :: String -> Iso AtomState AtomState
genInstance typeS = Iso (\(e@(Node _ name _),s) ->
                      let i = Node typeS ("rand"++name) noTv
                      in Just (i,(Link "InheritanceLink" [i,e] highTv):s))
                 (\(n,ls) ->  (\(Link _ [_,i] _) -> (i,ls)) `fmap` F.find (ff n) ls)
    where ff n (Link "InheritanceLink" [b,_] _) = n == b
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

--Various semi-isos to easily transfrom Certain Atom types
_eval :: Iso (Atom,[Atom]) Atom
_eval = eval . tolist2 . (second list)

_ctx :: Iso (Maybe Atom,Atom) Atom
_ctx = ((ctx . tolist2) ||| id) . ifJustA

_ctxold :: Iso (Atom,(Atom,[Atom])) Atom
_ctxold = ctx . tolist2 . (second _eval)

_ssl :: Iso (Atom,[Atom]) Atom
_ssl = ssl . tolist2 . addVarNode . _eval

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
linkIso n t = link . (Iso (\l -> Just (n,(l,t)))
                          (\(an,(l,at)) -> case an == n of
                                            True -> Just l
                                            False -> Nothing))

nodeIso :: String -> TruthVal -> Iso String Atom
nodeIso n t = node . (Iso (\l -> Just (n,(l,t)))
                          (\(an,(l,at)) -> case an == n of
                                            True -> Just l
                                            False -> Nothing))

concept = nodeIso "ConceptNode" noTv

predicate = nodeIso "PredicateNode" noTv

variable = nodeIso "VariableNode" noTv --is this even usefull?
