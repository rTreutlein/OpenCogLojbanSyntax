{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE TypeOperators      #-}
{-# LANGUAGE Rank2Types         #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE ScopedTypeVariables#-}
module Main where

import OpenCog.AtomSpace
import OpenCog.Lojban

import Control.Concurrent
import Control.Monad
import Control.Monad.IO.Class
import Control.Exception

import Main.Lojban
import Main.Atoms

main :: IO ()
main = do
    wordlist <- loadWordLists
    mainloop wordlist

mainloop :: WordList -> IO ()
mainloop wordlist= do
    putStrLn "Please Input some Lojban to Translate"
    input <- getLine
    (res :: Either SomeException Atom) <- try $ lojbanToAtomese wordlist input
    print res
    mainloop wordlist

