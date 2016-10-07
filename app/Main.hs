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

main :: IO ()
main = do
    (parser,printer) <- initParserPrinter
    mainloop parser printer

mainloop parser printer = do
    putStrLn "Please Input some Lojban to Translate"
    input <- getLine
    (res :: Either SomeException Atom) <- try $ parser input
    print res
    mainloop parser printer
    {-case res of
        Left _ -> mainloop parser printer
        Right atom -> do
            (res2 :: Either SomeException String) <- try $ printer atom
            print res2
            mainloop parser printer
-}
