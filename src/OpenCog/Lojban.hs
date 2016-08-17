{-# LANGUAGE LambdaCase                 #-}
module OpenCog.Lojban
    ( lojbanToAtomese
    , atomeseToLojban
    , WordList
    ) where


import OpenCog.Lojban.Syntax
import OpenCog.Lojban.Util

import OpenCog.AtomSpace

import Foreign.C
import Foreign.Ptr
import Control.Monad.IO.Class
import Control.Monad.Trans.Reader
import System.Random
import Data.Char (chr)
import qualified Data.Map as M

import Text.Syntax.Parser.Naive
import qualified Text.Syntax.Printer.Naive as P

lojbanToAtomese :: WordList -> String -> IO Atom
lojbanToAtomese state text = do
    atom <- post $ head $ parse (runReaderT preti state) text
    let anchor = case atom of
                    (Link "SatisfactionLink" _ _) -> "QuestionAnchor"
                    (Link "PutLink" _ _) -> "QuestionAnchor"
                    _ -> "StatementAnchor"
    return $ cLL [cAN anchor,atom]

atomeseToLojban :: WordList -> Atom -> String
atomeseToLojban state a@(LL [SL [SL s]]) = res
    where (Just res) = P.print (runReaderT preti state) $ head s

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
