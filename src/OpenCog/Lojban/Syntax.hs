{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE RelaxedPolyRec             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE TypeFamilies               #-}

module OpenCog.Lojban.Syntax where

import Prelude hiding (id,(.),(<*>),(<$>),pure,(*>),(<*))
import Data.Char
import Data.Foldable
import qualified Data.Foldable as F
import Data.List (partition)
import System.IO.Unsafe
import qualified Control.Arrow as A

import Control.Category (id,(.))
import Control.Isomorphism.Partial
import Control.Isomorphism.Partial.Unsafe
import Control.Isomorphism.Partial.TH
import Text.Syntax
import Text.Syntax.Parser.Naive
import qualified Text.Syntax.Printer.Naive as P

import OpenCog.AtomSpace
import OpenCog.Lojban.Selmaho
import OpenCog.Lojban.Util

import Debug.Trace

mytrace a = traceShow a a
mytrace2 s a = trace (s ++(' ':show a)) a

$(defineIsomorphisms ''Atom)

letter, digit :: Syntax delta => delta Char
letter  =  subset isLetter <$> token
digit   =  subset isDigit <$> token

--Handling for simple Strings
string :: Syntax delta => String -> delta String
string [] = nil <$> pure () <* optext " "
string (x:xs) = cons <$> (subset (== x) <$> token) <*> string xs

mytext :: Syntax delta => String -> delta ()
mytext s = text s <* optext " "

--Handles 1 of many options from a list
oneOf :: Syntax delta => (a -> delta b) -> [a] -> delta b
oneOf f [e] = f e
oneOf f (x:xs) = f x <|> oneOf f xs

--Handles words of the KOHA class
koha :: Syntax delta => delta String
koha = oneOf string kohas

--Handles words of the gismu class
gismu :: Syntax delta => delta String
gismu = oneOf string gismus

--Handles words of the A class
lojjohe :: Syntax delta => delta String
lojjohe = oneOf string lojjohes

--Handles words of the LE class
le :: Syntax delta => delta ()
le = oneOf mytext les

--Handles addtional arguments in a leP
beP :: Syntax delta => delta [(Atom,[Atom])]
beP = merge <$> mytext "be" *> sumtiP <*> many (mytext "bei" *> sumtiP) <* optext "be'o"
    where merge = Iso (\(a,b) -> Just (a:b)) (\(x:xs) -> Just (x,xs))

--((Atom,[Atom]),[(Atom,[Atom])])

--Handles anykind of LE phrases
leP :: Syntax delta => delta (Atom,[Atom])
leP = instanceOf . first _ssl . handleBE <$> le *> selbri <*> pure (Node "VariableNode" "$var" noTv) <*> optional beP <* optext "ku"

-- ((Pred,S),[Args]) -> ((pred,[args]),S)
-- ((Pred,S),([Args],Maybe [(Arg,S2)]) -> ((pred,[args]),S)

handleBE :: Iso (State,(Atom,Maybe [State])) ((Atom,[Atom]),[Atom])
handleBE = Iso (\((p,s1),(a1,mas1)) -> case mas1 of
                                        Just as1 -> let a = map fst as1
                                                        s = map snd as1
                                                    in Just ((p,a1:a),concat (s1:s))
                                        Nothing -> Just ((p,[a1]),s1))
               (\((p,a1:a),s) -> Just ((p,s),(a1,listToMaybe $ map (\e -> (e,s)) a)))
    where listToMaybe [] = Nothing
          listToMaybe a = Just a

--Handels all pronounses expect ma
kohaP1 :: Syntax delta => delta (Atom,[Atom])
kohaP1 = instanceOf . reorder0 . node <$> pure "ConceptNode" <*> koha <*> pure noTv

--Special case for the prounoun ma
--It is a fill the blank question so needs to be a Variable Node
ma :: Syntax delta => delta (Atom,[Atom])
ma = varInstance . reorder0 . node <$> pure "VariableNode" <*> (string "ma") <*> pure noTv

--KohaPharse for any kind of Pro-Noune
kohaP :: Syntax delta => delta (Atom,[Atom])
kohaP = kohaP1 <|> ma

noi :: Syntax delta => delta ()
noi = oneOf mytext nois

--This Handles relative phrases
ckini :: Syntax delta => delta (Atom,[Atom])
ckini = noi *> bridi <* optext "ku'o"

--This handles unconected sumti with optional relative phrases
sumti :: Syntax delta => delta (Atom,[Atom])
sumti =  ((kehaToSesku . handelCkini) ||| id) . ifJustB <$> (kohaP <|> leP) <*> optional ckini
    where handelCkini = Iso (\((a,b),(c,d)) -> Just (a,c:d++b))
                            (\(a,c:b) -> Just ((a,b),(c,b)))

-- (State,Maybe State) -> Either (State,State) (State)
-- ((Atom,[Atom]),Atom) -> State -> State

--This Handels Sumti connected by logical connectives
sumtiP :: Syntax delta => delta (Atom,[Atom])
sumtiP = ((first conLink . handleLojjohe) ||| id) . ifJustB <$> sumti <*> optional (lojjohe <*> sumtiP)
    where handleLojjohe = Iso (\((a1,s1),(con,(a2,s2))) -> Just ((con,[a1,a2]),s1++s2))
                              (\((con,[a1,a2]),s) -> Just ((a1,s),(con,(a2,s))))

--(State,Maybe (String,State)) -> (Either (State) (State,(String,State))
--(State,(String,State) -> ((String,[Atom]),[Atom]) -> (State)

selbri :: Syntax delta => delta (Atom,[Atom])
selbri = reorder0 . node <$> pure "PredicateNode" <*> gismu <*> pure noTv

tense :: Syntax delta => delta (Atom,[Atom])
tense = reorder0 . node <$> pure "ConceptNode" <*> oneOf string tenses <*> pure noTv

--THis Handles compelte sentences
bridi :: Syntax delta => delta (Atom,[Atom])
bridi =
    ((first _ctx . reorder2) ||| (first _eval . reorder1)) . ifJustA . mergeSumti
    <$> many1 sumtiP <*> optional tense <*> selbri <*> many sumtiP

preti :: Syntax delta => delta Atom
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

--For text that is both optional and should be parsed into ()
optext :: Syntax delta => String -> delta ()
optext t = (text (t++" ") <|> text t <|> text "")

--For dealing with maybes from/for Optional in the first or second position
ifJustA :: Iso (Maybe a,b) (Either (a,b) b)
ifJustA = Iso (\case {(Just a,b) -> Just $ Left (a,b) ; (Nothing,b) -> Just $  Right b})
              (\case {Left (a,b) -> Just (Just a,b) ;  Right b  -> Just (Nothing,b)})

ifJustB :: Iso (a,Maybe b) (Either (a,b) a)
ifJustB = Iso (\case {(a,Just b) -> Just $ Left (a,b) ; (a,Nothing) -> Just $  Right a})
              (\case {Left (a,b) -> Just $ (a,Just b) ;  Right a  -> Just $ (a,Nothing)})

--For mergin sumties before and after the selbri into a single list
mergeSumti :: (a ~ aa) => Iso ([a],(b,(c,[aa]))) (b,(c,[a]))
mergeSumti = Iso (\(a1,(b,(c,a2))) -> Just (b,(c,a1++a2)))
                 (\(b,(c,a)) -> case a of
                                [] -> Nothing
                                (x:xs) -> Just ([x],(b,(c,xs)))
                 )


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
type State = (Atom,[Atom])

--Many of the Iso take/result in (Atom,[Atom])
--The following reorder functions merge the list of Atoms into 1
--And creates a tuple with all the single Atoms in the first element of the tuple
reorder0 :: Iso Atom State
reorder0 = Iso (\a -> Just (a,[]))
               (\(a,_) -> Just a)

reorder1 :: Iso (State,[State]) ((Atom,[Atom]),[Atom])
reorder1 = Iso (\((a,s),ls) -> let fs = map fst ls
                                   sn = map snd ls
                               in Just ((a,fs),concat $ s:sn))
               (\((a,fs),s) -> Just ((a,s),map (\a -> (a,s))fs))

reorder2 :: Iso (State,(State,[State])) ((Atom,(Atom,[Atom])),[Atom])
reorder2 = Iso (\((a1,s1),((a2,s2),ls)) -> let fs = map fst ls
                                               sn = map snd ls
                                           in Just ((a1,(a2,fs)),concat $ s1:s2:sn))
               (\((a1,(a2,fs)),s) -> Just ((a1,s),((a2,s),map (\a -> (a,s)) fs)))

--If we have a relative clause
--this will switch the ke'a with the actually concept
kehaToSesku :: Iso State State
kehaToSesku = Iso (\(c,l) -> case partition tf l of
                                ([],_) -> Nothing
                                ([a],b)  ->Just (c,f kea c a : b)
                                _ -> error "This is not implemented yet.")
                  (\(c,l) -> case partition tf l of
                                ([],_) -> Nothing
                                ([a],b)  -> Just (c,f c kea a : b)
                                _ -> error "This is not implemented yet.")
    where kea = Node "ConceptNode" "ke'a" noTv
          f a b e = atomMap (\c -> if c == a then b else c) e
          tf (Link "EvaluationLink" _ _) = True
          tf (Link "ContextLink" _ _) = True
          tf a = False

--Most pronouns are instances of a more general conecpt
--This will create the inheritance link to show this relation
instanceOf :: Iso State State
instanceOf = genInstance "ConceptNode"

varInstance :: Iso State State
varInstance = genInstance "VariableNode"

genInstance :: String -> Iso State State
genInstance typeS = Iso (\(e,s) ->
                      let i = Node typeS "rand" noTv
                      in Just (i,(Link "InheritanceLink" [i,e] highTv):s))
                 (\(n,ls) ->  (\(Link _ [_,i] _) -> (i,ls)) `fmap` find (ff n) ls)
    where ff n (Link "InheritanceLink" [b,_] _) = n == b
          ff n a = False

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

func :: NotLinked [Atom] String -> Atom -> Linked [Atom] String
func al@(NotLinked a) (Link "AndLink" [e1,e2] noTv) = Linked (a:e1) "AndLink" $ addElem e2 al
func al@(Linked a1 b l) (Link "AndLink" [e1,e2] noTv) =
    Linked (a1:e1) "AndLink" $ addElem e2 al
func l b = addElem b l

--Various semi-isos to easily parse/print Certain Atom types
_eval :: Iso (Atom,[Atom]) Atom
_eval = eval . tolist2 . (second list)

_ctx :: Iso (Atom,(Atom,[Atom])) Atom
_ctx = ctx . tolist2 . (second _eval)

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
