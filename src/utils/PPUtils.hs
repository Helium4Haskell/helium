module PPUtils
    (   commas, utrechtList
    ,   commasOr
    ,   commasAnd
    ,   commasWord
    ,   semicolons, vsemicolons
    ,   inQuotes
    ,   module PPrint
    ) where {

import PPrint;

----
-- Pretty-printing
----

commas :: [Doc] -> Doc;
commas docs =
    hcat (punctuate (comma <+> empty) docs);

semicolons :: [Doc] -> Doc;
semicolons docs =
    hcat (punctuate (text "; ") docs);

vsemicolons :: [Doc] -> Doc;
vsemicolons docs =
    vcat (punctuate (text "; ") docs);

utrechtList :: Doc -> Doc -> [Doc] -> Doc;
utrechtList start end []     = empty;
utrechtList start end (d:ds) =
    let {
        utrechtList' []     = end;
        utrechtList' (d:ds) = comma <+> d <$> utrechtList' ds;
    } in
        start <+> d <$> utrechtList' ds;

commasOr :: [Doc] -> Doc;
commasOr docs = commasWord "or" docs;

commasAnd :: [Doc] -> Doc;
commasAnd docs = commasWord "and" docs;

commasWord :: String -> [Doc] -> Doc;
commasWord _ [] =
    empty;
commasWord _ [doc] =
    doc;
commasWord word docs =
    let
    {
        (initDocs, lastDoc) = splitAt (length docs - 1) docs
    }
    in
        commas initDocs <+> text word <+> head lastDoc;

inQuotes = 
    squotes . text;
}