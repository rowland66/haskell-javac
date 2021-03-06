{-# LANGUAGE RecordWildCards #-}

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
import Data.List (foldl,foldl')
import TypeValidator
import TypeInfo (Type(..))

data Environment = Environment {variableTypeMap :: Map.Map P.SimpleName Type
                               , variablePositionMap :: Map.Map P.SimpleName Int
                               , typeData :: ValidTypeClassData
                               } deriving (Show)

createMethodEnvironment :: ValidTypeClassData -> ValidTypeClazz -> ValidTypeMethod -> Environment
createMethodEnvironment typeData clazz@ValidTypeClazz {..} ValidTypeMethod {..} =
  let (superClass, _) = vcParent
      env = Map.insert P.createNameThis (L vcName)
        $ Map.insert P.createNameSuper (L superClass)
        $ foldr (\ValidTypeParameter {..} env -> Map.insert (fst vpName) (L vpType) env) Map.empty vmParams
      (_, envPos') = foldl' (\(i, env) ValidTypeParameter {..} -> (i+1, Map.insert (fst vpName) i env)) (1, Map.empty) vmParams
      envPos = Map.insert P.createNameThis 0 envPos' in
  Environment {variableTypeMap=env, variablePositionMap=envPos, typeData=typeData}

createConstructorEnvironmentRight :: ValidTypeClassData -> ValidTypeClazz -> ValidTypeMethod -> Environment
createConstructorEnvironmentRight typeData ValidTypeClazz {..} ValidTypeMethod {..} =
  let env = foldr (\ValidTypeParameter {..} env -> Map.insert (fst vpName) (L vpType) env) Map.empty vmParams
      (_, envPos') = foldl (\(i, env) ValidTypeParameter {..} -> (i+1, Map.insert (fst vpName) i env)) (1, Map.empty) vmParams
      envPos = Map.insert P.createNameThis 0 envPos' in
  Environment {variableTypeMap=env, variablePositionMap=envPos, typeData=typeData}


createConstructorEnvironmentLeft :: ValidTypeClassData -> ValidTypeClazz -> Environment
createConstructorEnvironmentLeft typeData ValidTypeClazz {..} =
  let env = Map.insert P.createNameThis (L vcName) Map.empty
      envPos = Map.insert P.createNameThis 0 Map.empty in
  Environment {variableTypeMap=env, variablePositionMap=envPos, typeData=typeData}

(!?) :: Environment -> P.SimpleName -> Maybe (Type,Int)
(!?) Environment {variableTypeMap=env, variablePositionMap=envPos, typeData=typeData} variable =
  case env Map.!? variable of
    Just tp -> Just (tp, envPos Map.! variable)
    Nothing -> Nothing