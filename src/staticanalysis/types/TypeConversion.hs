-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- TypeConversion.hs : A module to convert between UHA_Type and Tp
--
-------------------------------------------------------------------------------

module TypeConversion where

import UHA_Utils (getNameName, nameFromString)
import UHA_Range (noRange)
import Utils (internalError)
import List (union)
import UHA_Syntax
import Types

----------------------------------------------------------------------
-- conversion functions from and to UHA

namesInTypes :: Types -> Names
namesInTypes = foldr union [] . map namesInType

namesInType :: Type -> Names
namesInType uhaType = case uhaType of

      Type_Application _ _ fun args -> namesInTypes (fun : args)                                                 
      Type_Variable _ name          -> [name]      
      Type_Constructor _ _          -> []
      Type_Parenthesized _ t        -> namesInType t                    
      Type_Qualified _ _ _          -> internalError "SATypes.hs" "namesInType" "qualified types are currently not supported"
      Type_Forall _ _ _             -> internalError "SATypes.hs" "namesInType" "universal types are currently not supported"            
      Type_Exists _ _ _             -> internalError "SATypes.hs" "namesInType" "existential types are currently not supported"
      
-- name maps play an important role in converting since they map UHA type variables (string) to TVar's (int)  
makeNameMap :: Names -> [(Name,Tp)]
makeNameMap = flip zip (map TVar [0..])

makeTpSchemeFromType :: Type -> TpScheme
makeTpSchemeFromType uhaType = 
   let nameMap = makeNameMap (namesInType uhaType)
       tp = makeTpFromType nameMap uhaType
   in TpScheme (ftv tp) [ (i,getNameName n) | (n,TVar i) <- nameMap] ([] :=> tp)

makeTpFromType :: [(Name,Tp)] -> Type -> Tp    
makeTpFromType nameMap = rec 
  where                    
        rec :: Type -> Tp
        rec uhaType = case uhaType of  
             Type_Application _ _ fun args -> foldl TApp (rec fun) (map rec args)
             Type_Variable _ name          -> maybe (TCon "???") id (lookup name nameMap)                                                      
             Type_Constructor _ name       -> TCon (getNameName name)
             Type_Parenthesized _ t        -> rec t                                                 
             Type_Qualified _ _ _          -> internalError "SATypes.hs" "makeTpFromType" "qualified types are currently not supported"
             Type_Forall _ _ _             -> internalError "SATypes.hs" "makeTpFromType" "universal types are currently not supported"            
             Type_Exists _ _ _             -> internalError "SATypes.hs" "makeTpFromType" "existential types are currently not supported"

convertFromSimpleTypeAndTypes :: SimpleType -> Types -> (Tp,Tps)
convertFromSimpleTypeAndTypes stp  tps = 
   let SimpleType_SimpleType _ name typevariables = stp
       nameMap    = makeNameMap (foldr union [] (typevariables : map namesInType tps))
       simpletype = foldl TApp (TCon (getNameName name)) (take (length typevariables) (map TVar [0..]))
   in (simpletype,map (makeTpFromType nameMap) tps)
       
makeTypeFromTp :: Tp -> Type
makeTypeFromTp t = 
    let (x,xs) = leftSpine t 
    in if null xs 
        then f x
        else Type_Application noRange True (f x) (map makeTypeFromTp xs)
   where f (TVar i) = Type_Variable noRange    (nameFromString ('v' : show i)) 
         f (TCon s) = Type_Constructor noRange (nameFromString s)
