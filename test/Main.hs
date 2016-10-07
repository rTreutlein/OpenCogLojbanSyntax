{-# LANGUAGE ScopedTypeVariables#-}

module Main where

import OpenCog.AtomSpace
import OpenCog.Lojban

import Control.Exception
import Control.Monad

import System.Exit (exitFailure,exitSuccess)

main :: IO ()
main = do
    putStrLn "Starting Test"
    (parser,printer) <- initParserPrinter
    sentences <- loadData
  --testRes <- mapM (pptest parser printer) sentences
    testRes <- mapM (ptest parser) sentences
    let testResF  = filter id testRes
    putStrLn $
        "Of " ++ (show $ length sentences) ++ " sentences " ++
        (show $ length testResF) ++ " have been parsed/printed successfully."
    case (length testResF) == (length sentences) of
        True  -> exitSuccess
        False -> exitFailure

ptest :: (String -> IO Atom) -> String -> IO Bool
ptest parser text = do
    print text
    (parsed :: Either SomeException Atom) <- (try . parser) text
    case parsed of
        Left _    -> print False >> return False
        Right res -> print True  >> return True

pptest :: (String -> IO Atom) -> (Atom -> IO String) -> String -> IO Bool
pptest parser printer text = do
    (parsed :: Either SomeException Atom) <- (try . parser) text
    case parsed of
        Left _    -> return False
        Right res -> do
            (eptext :: Either SomeException String) <- try $ printer res
            case eptext of
                Left _ -> print text >> return False
                Right ptext -> do
                    case ptext == text of
                        True -> return True
                        False -> print text >> print ptext >> return False

loadData :: IO [String]
loadData = do
    file <- readFile "data.txt"
    return (lines file)

isRight :: Either a b -> Bool
isRight (Left  _) = False
isRight (Right _) = True
