module Main.Lojban where

import Text.XML.HXT.Core
import qualified Data.Map as M

loadWordLists :: IO (M.Map String [String],[String])
loadWordLists = do
    let src = "lojban.xml"
    gismu <- runX (readDocument [] src >>> getChildren >>> getValsi >>> getGismu)
    cmavo <- runX (readDocument [] src >>> getChildren >>> getValsi >>> getCmavo)
    let selmahos = M.fromListWith (++) $ map f cmavo
        f (s,c) = (takeWhile p s,[c])
        p e = e `notElem` "1234567890*"
        src = "/usr/local/share/opencog/lojban.xml"
    return (selmahos,gismu)

getGismu :: ArrowXml a => a XmlTree String
getGismu = hasAttrValue "type" ((||) <$> (== "gismu") <*>
                               ((||) <$> (== "lujvo") <*> (== "fu'ivla")))
           >>>
           getAttrValue "word"

getCmavo :: ArrowXml a => a XmlTree (String,String)
getCmavo = hasAttrValue "type" (== "cmavo")
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
