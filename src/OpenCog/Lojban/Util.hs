{-# LANGUAGE PatternSynonyms    #-}
module OpenCog.Lojban.Util where

import OpenCog.AtomSpace

mapFst :: (a -> b) -> (a,c) -> (b,c)
mapFst f (a,c) = (f a,c)

mapSnd :: (a -> b) -> (c,a) -> (c,b)
mapSnd f (c,a) = (c,f a)

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

infixl 8 ...
(...) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
(...) = (.).(.)

pattern CN name <-Node "ConceptNode" name _
pattern PN name <-Node "PredicateNode" name _
pattern GPN name <-Node "GroundedPredicateNode" name _
pattern VN name <-Node "VariableNode" name _

pattern AL l <- Link "AndLink" l _
pattern LL l <- Link "ListLink" l _
pattern ImpL l tv <- Link "ImplicationLink" l tv
pattern InhL l tv <- Link "InheritanceLink" l tv
pattern SL l <- Link "SetLink" l _
pattern SSL l <- Link "SatisfyingSetLink" [l] _
pattern EvalL p a <- Link "EvaluationLink" [p,a] _
pattern CtxL c a <- Link "ContextLink" [c,a] _
pattern SimL a b <- Link "SimilarityLink" [a,b] _
pattern SubL a b <- Link "SubSetLink" [a,b] _
pattern LambdaL a b <- Link "LambdaLink" [a,b] _

cCN name tv = Node "ConceptNode" name tv
cPN name tv = Node "PredicateNode" name tv
cGPN name tv = Node "GroundedPredicateNode" name tv
cVN name    = Node "VariableNode" name noTv
cAN name    = Node "AnchorNode" name noTv
cNN name    = Node "NumberNode" name noTv

cLL a           = Link "ListLink"                             a     noTv
cSL a           = Link "SetLink"                              a     noTv
cVL a           = Link "VariableList"                         a     noTv
cInhL tv a b    = Link "InheritanceLink"                  [a,b]     tv
cImpL tv a b    = Link "ImplicationLink"                  [a,b]     tv
cIFaoIFL tv a b = Link "AndLink"          [cImpL tv a b,cImpL tv b a] tv
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


mkCtxPre pred atom = Link "EquivalenceLink"
                        [cLamdaL highTv
                            (cVN "1")
                            (cEvalL highTv
                                (pred)
                                (cLL [cVN "1"]))
                        ,cLamdaL highTv
                            (cVN "2")
                            (cCtxL highTv
                                (cVN "2")
                                (atom))
                        ] highTv

pattern CtxPred atom <- Link "EquivalenceLink"
                                [ _
                                , LambdaL _ (CtxL _ (atom))
                                ] _


