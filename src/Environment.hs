module Environment
  ( Environment
  , createMethodEnvironment
  , createConstructorEnvironmentRight
  , createConstructorEnvironmentLeft
  , (!?)
  , (!!?)
  ) where

import qualified Data.Map.Strict as Map
import Parser2

data Environment = Environment {variableTypeMap :: (Map.Map String DataType), variablePositionMap :: (Map.Map String Int), classMap :: (Map.Map String Clazz2)} deriving (Show)

createMethodEnvironment :: (Map.Map String Clazz2) -> Clazz2 -> Method -> Environment
createMethodEnvironment classMap clazz@(NewClazz2 _ className _ _ _ _) (NewMethod _ _ params _ _ _) =
  let env = Map.insert "this" className $ foldr (\(NewParameter _ tp nm) env -> Map.insert nm tp env) Map.empty params
      (_, envPos') = (foldl (\(i, env) (NewParameter _ _ nm) -> (i+1, Map.insert nm i env)) (1, Map.empty) params)
      envPos = Map.insert "this" 0 envPos' in
  Environment {variableTypeMap=env, variablePositionMap=envPos, classMap=classMap}

createConstructorEnvironmentRight :: (Map.Map String Clazz2) -> Clazz2 -> Constructor -> Environment
createConstructorEnvironmentRight classMap (NewClazz2 _ className _ _ _ _) (NewConstructor _ params _ _ _) =
  let env = foldr (\(NewParameter _ tp nm) env -> Map.insert nm tp env) Map.empty params
      (_, envPos') = (foldl (\(i, env) (NewParameter _ _ nm) -> (i+1, Map.insert nm i env)) (1, Map.empty) params)
      envPos = Map.insert "this" 0 envPos' in
  Environment {variableTypeMap=env, variablePositionMap=envPos, classMap=classMap}


createConstructorEnvironmentLeft :: (Map.Map String Clazz2) -> Clazz2 -> Environment
createConstructorEnvironmentLeft classMap (NewClazz2 _ className _ _ _ _) =
  let env = (Map.insert "this" className Map.empty)
      envPos = (Map.insert "this" 0 Map.empty) in
  Environment {variableTypeMap=env, variablePositionMap=envPos, classMap=classMap}

(!?) :: Environment -> String -> (Maybe (DataType,Int))
(!?) Environment {variableTypeMap=env, variablePositionMap=envPos, classMap=classMap} variable =
  case (env Map.!? variable) of
    Just tp -> Just (tp, (envPos Map.! variable))
    Nothing -> Nothing

(!!?) :: Environment -> String -> (Maybe (Clazz2,Int))
(!!?) env@Environment {variableTypeMap=varMap, classMap=classMap} variable = (fmap (\(tp,ndx) -> (classMap Map.! tp,ndx)) (env !? variable))

(<!>) :: Environment -> String -> (Maybe Int)
(<!>) Environment {variablePositionMap=env, classMap=classMap} variable = (env Map.!? variable)
