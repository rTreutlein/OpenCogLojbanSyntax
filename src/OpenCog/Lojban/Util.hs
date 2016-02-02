{-# LANGUAGE PatternSynonyms    #-}
module OpenCog.Lojban.Util where

import OpenCog.AtomSpace


--Move this to the Haskell Bindings
--Allows easy mapping over the Nodes inside of a link
atomMap :: (Atom -> Atom) -> Atom -> Atom
atomMap f (Link t ls tv) = Link t (map (atomMap f) ls) tv
atomMap f n@(Node _ _ _) = f n

atomMapM :: Monad m => (Atom -> m Atom) -> Atom -> m Atom
atomMapM f (Link t ls tv) = do
    nls <- (mapM (atomMapM f) ls)
    pure $ Link t nls tv
atomMapM f n@(Node _ _ _) = f n

atomFold :: (a -> Atom -> a) -> a -> Atom -> a
atomFold f v (Link t ls tv) = foldl (atomFold f) v ls
atomFold f v n@(Node _ _ _) = f v n

highTv :: TruthVal
highTv = stv 1 0.9

lowTv :: TruthVal
lowTv = stv 0.000001 0.01

if' :: Bool -> a -> a -> a
if' True a _ = a
if' False _ a = a

infixr 1 ?
(?) :: Bool -> a -> a -> a
(?) = if'

pattern CN name <-Node "ConceptNode" name _
pattern PN name <-Node "PredicateNode" name _
pattern VN name <-Node "VariableNode" name _

pattern AL l <- Link "AndLink" l _
pattern LL l <- Link "ListLink" l _
pattern SL l <- Link "SetLink" l _
pattern SSL l <- Link "SatisfyingSetLink" [l] _
pattern EvalL p a <- Link "EvaluationLink" [p,a] _
pattern CtxL c a <- Link "ContextLink" [c,a] _
pattern SimL a b <- Link "SimilarityLink" [a,b] _
pattern SubL a b <- Link "SubSetLink" [a,b] _

cCN name tv = Node "ConceptNode" name tv
cPN name tv = Node "PredicateNode" name tv
cVN name    = Node "VariableNode" name noTv
cAN name    = Node "AnchorNode" name noTv
cNN name    = Node "NumberNode" name noTv

cLL a           = Link "ListLink"                             a     noTv
cSL a           = Link "SetLink"                              a     noTv
cInL tv a b     = Link "InheritanceLink"                  [a,b]     tv
cImL tv a b     = Link "ImplicationLink"                  [a,b]     tv
cIFaoIFL tv a b = Link "AndLink"          [cImL tv a b,cImL tv b a] tv
cEvalL tv a b   = Link "EvaluationLink"                   [a,b]     tv
cSSL tv a       = Link "SatisfyingSetLink"                  [a]     tv
cExL tv a b     = Link "ExistsLink"                       [a,b]     tv
cFAL tv a b     = Link "ForAllLink"                       [a,b]     tv
cPL     a b     = Link "PutLink"                          [a,b]     noTv
cGL     a       = Link "GetLink"                            [a]     noTv
cAL  tv a       = Link "AndLink"                                  a tv
cOL  tv a       = Link "OrLink"                                   a tv
cNL  tv a       = Link "NotLink"                                [a] tv
cCtxL tv a b    = Link "ContextLink"                      [a,b]     tv
cLamdaL tv a b  = Link "LambdaLink"                       [a,b]     tv

