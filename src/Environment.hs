module Environment
  ( Environment
  , createMethodEnvironment
  , createConstructorEnvironmentRight
  , createConstructorEnvironmentLeft
  , (!?)
  ) where

import qualified Data.Map.Strict as Map
import qualified Parser2 as P2
import ClassPath
import qualified Parser as P
import Data.List (foldl')
import TypeInfo

data Environment = Environment {variableTypeMap :: Map.Map P.SimpleName Type
                               , variablePositionMap :: Map.Map P.SimpleName Int
                               , typeData :: ClassData
                               } deriving (Show)

type ClassData = (ClassPath,P2.LocalClasses)

createMethodEnvironment :: ClassData -> P2.Clazz2 -> P2.Method -> Environment
createMethodEnvironment typeData clazz@(P2.NewClazz2 pos _ className _ _ _) (P2.NewMethod _ _ params _ _ _) =
  let env = Map.insert P.createNameThis (L className (P2.SourcePos' pos)) $ foldr (\(P2.NewParameter pos tp nm) env -> Map.insert nm (L tp (P2.SourcePos' pos)) env) Map.empty params
      (_, envPos') = foldl' (\(i, env) (P2.NewParameter _ _ nm) -> (i+1, Map.insert nm i env)) (1, Map.empty) params
      envPos = Map.insert P.createNameThis 0 envPos' in
  Environment {variableTypeMap=env, variablePositionMap=envPos, typeData=typeData}

createConstructorEnvironmentRight :: ClassData -> P2.Clazz2 -> P2.Method -> Environment
createConstructorEnvironmentRight typeData (P2.NewClazz2 _ _ className _ _ _) (P2.NewMethod _ _ params _ _ _) =
  let env = foldr (\(P2.NewParameter pos tp nm) env -> Map.insert nm (L tp (P2.SourcePos' pos)) env) Map.empty params
      (_, envPos') = foldl (\(i, env) (P2.NewParameter _ _ nm) -> (i+1, Map.insert nm i env)) (1, Map.empty) params
      envPos = Map.insert P.createNameThis 0 envPos' in
  Environment {variableTypeMap=env, variablePositionMap=envPos, typeData=typeData}


createConstructorEnvironmentLeft :: ClassData -> P2.Clazz2 -> Environment
createConstructorEnvironmentLeft typeData (P2.NewClazz2 pos  _ className _ _ _) =
  let env = Map.insert P.createNameThis (L className (P2.SourcePos' pos)) Map.empty
      envPos = Map.insert P.createNameThis 0 Map.empty in
  Environment {variableTypeMap=env, variablePositionMap=envPos, typeData=typeData}

(!?) :: Environment -> P.SimpleName -> Maybe (Type,Int)
(!?) Environment {variableTypeMap=env, variablePositionMap=envPos, typeData=typeData} variable =
  case env Map.!? variable of
    Just tp -> Just (tp, envPos Map.! variable)
    Nothing -> Nothing
{--
(!!?) :: Environment -> P.SimpleName -> Maybe (P2.Clazz2,Int)
(!!?) env@Environment {variableTypeMap=varMap, typeData=typeData} variable = fmap (\(tp,ndx) -> (classMap Map.! tp,ndx)) (env !? variable)

(<!>) :: Environment -> P.SimpleName -> Maybe Int
(<!>) Environment {variablePositionMap=env, typeData=typeData} variable = env Map.!? variable
-}