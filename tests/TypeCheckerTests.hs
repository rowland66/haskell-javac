module Main where

import Test.HUnit
import Test.Framework
import Test.Framework.Providers.HUnit
import qualified Data.Text as T
import qualified Data.Map as M
import Control.Monad.Trans.State.Strict (StateT,get,put,evalStateT)
import Control.Monad.Trans.Class (lift)
import Control.Exception (AssertionFailed(AssertionFailed))

import TypeCheckerTypes
import TypeChecker
import ClassPath

test1 :: StateT ClassPath IO ()
test1 = do
  maybeClass1 <- getClass (T.pack "java/util/HashMap")
  case maybeClass1 of
    Nothing -> lift (assertFailure "Failed to load class")
    Just vtqn -> do
      lift $ assertEqual "loaded HashMap" "java/util/HashMap" (show (getValidTypeQName vtqn))

test2 :: StateT ClassPath IO ()
test2 = do
  classpath <- get
  maybeClassList <- sequence [getClass (T.pack "java/lang/Integer"), getClass (T.pack "java/lang/Number")]
  let maybeClassList' = sequence maybeClassList
  case maybeClassList' of
    Nothing -> lift (assertFailure "Failed to load class")
    Just classList -> do
      let integerVtnw = (head classList)
          numberVtnw = (head (tail classList))
      supertypeSet <- lift $
        evalStateT 
          (getSupertypeSet (TypeCheckerClassReferenceTypeWrapper integerVtnw Nothing)) 
          (classpath, M.empty)
      lift $ assertBool
        "java/lang/Number is super type of java/lang/Integer"
        ("java/lang/Number" `elem` fmap (show . getValidTypeQName . getTypeCheckerClassReferenceTypeClassName) supertypeSet)
      lift $ assertBool
        "java/lang/Object is super type of java/lang/Integer"
        ("java/lang/Object" `elem` fmap (show . getValidTypeQName . getTypeCheckerClassReferenceTypeClassName) supertypeSet)

test3 :: StateT ClassPath IO ()
test3 = do
  classpath <- get
  maybeClassList <- sequence [getClass (T.pack "java/lang/Integer"), getClass (T.pack "java/lang/Number")]
  let maybeClassList' = sequence maybeClassList
  case maybeClassList' of
    Nothing -> lift (assertFailure "Failed to load class")
    Just classList -> do
      let integerVtnw = (head classList)
          numberVtnw = (head (tail classList))
      isSubType <- lift $ 
        evalStateT 
          (isSubtypeOf 
            (TypeCheckerClassReferenceTypeWrapper integerVtnw Nothing) 
            (TypeCheckerClassReferenceTypeWrapper numberVtnw Nothing)) 
          (classpath, M.empty)
      lift $ assertBool
        "java/lang/Integer is a subtype of java/lang/Number"
        isSubType

main :: IO ()
main = do
  classPath <- createClassPath "out3/classes"
  defaultMain
    [ testCase "load class from classpath" (evalStateT test1 classPath)
    , testCase "super type set" (evalStateT test2 classPath)
    , testCase "subtype" (evalStateT test3 classPath)
    ]

getClass :: T.Text -> StateT ClassPath IO (Maybe TypeCheckerValidTypeQualifiedNameWrapper)
getClass qualifiedName = do
  let packageList = if length list > 1 then take (length list - 1) list else []
        where list = T.split (=='/') qualifiedName
      className = if length list > 1 then head (drop (length list - 1) list) else head list
        where list = T.split (=='/') qualifiedName

  classPath <- get
  return $
    getClassPathClassType classPath (QualifiedName packageList (SimpleName className))
