module OpenCog.Lojban.Selmaho where

import Data.Serialize
import Data.ByteString.Lazy

import Prelude hiding (readFile)
import qualified Data.Map as M

loadSelmaho :: String -> IO (M.Map String [String])
loadSelmaho s = do
    file <- readFile s
    pure $ case decodeLazy file of
            Left e -> error e
            Right m -> m

kohas = ["mi","do","ti","ke'a","tic"]

les = ["lo","le"]

las = ["la"]

kus = ["ku"]

gismus = ["jimpe","nelci","gerku"]

tenses = ["pu","ca","vi"]

nois = ["noi","poi","voi"]

lojjohes = ["e","a"]
