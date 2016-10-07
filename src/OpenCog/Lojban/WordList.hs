module OpenCog.Lojban.WordList where

import Text.XML.HXT.Core
import qualified Data.Map as M
import Data.List

loadWordLists :: IO (M.Map String [String],[String],[(String,String)])
loadWordLists = do
    let src = "lojban.xml"
    gismu <- runX (readDocument [] src >>> getChildren >>> getValsi >>> getGismu)
    cmavo <- runX (readDocument [] src >>> getChildren >>> getValsi >>> getCmavo)
    bai   <- runX (readDocument [] src >>> getChildren >>> getValsi >>> getBAI)
    let selmahos = M.fromListWith (++) $ map f cmavo
        f (s,c) = (takeWhile p s,[c])
        p e = e `notElem` "1234567890*"
        src = "/usr/local/share/opencog/lojban.xml"
    return (selmahos,gismu,map handleBAIprefix bai)

handleBAIprefix :: (String,String) -> (String,String)
handleBAIprefix (b,d) = if t2 `elem` se then (b,t2 ++ ' ' : d) else (b,d)
    where se = ["se","te","ve","xe"]
          t2 = take 2 b

getGismu :: ArrowXml a => a XmlTree String
getGismu = hasAttrValue "type" ((||) <$> (== "gismu") <*>
                               ((||) <$> (== "lujvo") <*> (== "fu'ivla")))
           >>>
           getAttrValue "word"

isCmavo :: ArrowXml a => a XmlTree XmlTree
isCmavo = hasAttrValue "type" (isPrefixOf "cmavo")

getCmavo :: ArrowXml a => a XmlTree (String,String)
getCmavo = isCmavo
           >>>
           (getChildren >>> hasName "selmaho" /> getText)
           &&&
           getAttrValue "word"

getValsi :: ArrowXml a => a XmlTree XmlTree
getValsi = hasName "dictionary"
           />
           hasName "direction"
           />
           hasName "valsi"

getBAI :: ArrowXml a => a XmlTree (String,String)
getBAI = isCmavo
         >>>
         guards (getChildren >>> deep (hasText $ isPrefixOf "BAI"))
                (arr id)
         >>>
         getAttrValue "word"
         &&&
         (getChildren >>> hasName "definition" /> getText >>> arr (takeWhile ((/=) ' ')))
