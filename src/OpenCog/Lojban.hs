{-# LANGUAGE LambdaCase                 #-}
module OpenCog.Lojban where

import OpenCog.Lojban.Syntax
import OpenCog.Lojban.Util

import Text.Syntax.Parser.Naive
import qualified Text.Syntax.Printer.Naive as P

import OpenCog.AtomSpace
import Foreign.C
import Foreign.Ptr
import Control.Monad.IO.Class
import System.Random
import Data.Char (chr)

foreign export ccall "lojbanToAtomese"
    c_lojbanToAtomese :: Ptr AtomSpaceRef -> UUID -> IO (UUID)

c_lojbanToAtomese = exportFunction lojbanToAtomese

foreign export ccall "atomeseToLojban"
    c_atomeseToLojban :: Ptr AtomSpaceRef -> UUID -> IO (UUID)

c_atomeseToLojban = exportFunction atomeseToLojban

lojbanToAtomese :: Atom -> AtomSpace Atom
lojbanToAtomese (LL [SL []])         = return $ cSL []
lojbanToAtomese (LL [SL [CN text ]]) = do
    atom <- liftIO $ post $ head $ parse preti text
    let anchor = case atom of
                    (Link "SatisfactionLink" _ _) -> "QuestionAnchor"
                    (Link "PutLink" _ _) -> "QuestionAnchor"
                    _ -> "StatementAnchor"
    return $ Link "ListLink" [Node "AnchorNode" anchor noTv,atom] noTv
lojbanToAtomese a = error $ "input was in the wrong format, expecting a ConceptNode got:" ++ show a

atomeseToLojban :: Atom -> AtomSpace Atom
atomeseToLojban a@(LL [SL [SL s]]) = do
    liftIO $ print a
    let (Just lojban) = P.print preti $ head s
    return $ cLL [cAN "LojbanAnswer"
            ,cCN lojban noTv
            ]
atomeseToLojban a@(LL [SL [sat]]) = do
    liftIO $ print a
    mtv <- evaluate sat
    let lojban = case mtv of
            Just tv -> tvToLojban tv
            Nothing -> "mi na djuno (this might be an error)"
    return $ cLL [cAN "LojbanAnswer"
            ,cCN lojban noTv
            ]
atomeseToLojban a = do
    liftIO $ print a
    return $ cSL []

tvToLojban :: TruthVal -> String
tvToLojban tv
    | (tvMean tv) > 0.5 = "go'i"
    | (tvMean tv) <= 0.5 = "nago'i"

post :: Atom -> IO Atom
post a = atomMapM (\case {(Node "ConceptNode" "rand" tv) ->
                            randName >>= (\n -> pure $ Node "ConceptNode" n tv);
                         e -> pure $ e}) a

randName :: IO String
randName = do
    std <- getStdGen
    let name = take 20 $ map chr $ randomRs (33,126) std
    pure name
