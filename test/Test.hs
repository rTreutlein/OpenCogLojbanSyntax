module Test where

import Prelude hiding (id,(.),(<*>),(<$>),pure,(*>),(<*),foldl,print)
import qualified Prelude as P

import OpenCog.Lojban
import OpenCog.Lojban.Syntax
import OpenCog.Lojban.Util
import OpenCog.Lojban.WordList

import OpenCog.AtomSpace

import Text.Syntax
import Text.Syntax.Parser.Naive
import Text.Syntax.Printer.Naive

import Control.Monad.Trans.Reader
import Control.Category (id,(.))

import Control.Isomorphism.Partial

import Text.XML.HXT.Core


myinit = do
    wordlist <- loadWordLists
    let myparse x y = parse (runReaderT x wordlist) y
        myprint x y = print (runReaderT x wordlist) y
    return (myparse,myprint)
