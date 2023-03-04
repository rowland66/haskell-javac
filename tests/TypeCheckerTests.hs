module Main where

import Test.HUnit
import Test.Framework
import Test.Framework.Providers.HUnit
import qualified Data.Text as T
import qualified Data.Map as M
import qualified Data.Vector as V
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
          (getOrderedParentTypes (TypeCheckerClassReferenceTypeWrapper integerVtnw Nothing)) 
          (classpath, M.empty)
      lift $ assertBool
        "java/lang/Number is super type of java/lang/Integer"
        ("java/lang/Number" `elem` fmap (show . getValidTypeQName . getTypeCheckerClassReferenceTypeClassName) supertypeSet)
      lift $ assertBool
        "java/lang/Object is super type of java/lang/Integer"
        ("java/lang/Object" `elem` fmap (show . getValidTypeQName . getTypeCheckerClassReferenceTypeClassName) supertypeSet)

subtypeTest :: String -> String -> StateT ClassPath IO Bool
subtypeTest child parent = subtypeTestWithTypeParams child [] parent []

subtypeTestWithTypeParams :: String -> [TypeCheckerTypeArgument] -> String -> [TypeCheckerTypeArgument] -> StateT ClassPath IO Bool
subtypeTestWithTypeParams child childTypeArgs parent parentTypeArgs = do
  classpath <- get
  maybeClassList <- sequence [getClass (T.pack child), getClass (T.pack parent)]
  let maybeClassList' = sequence maybeClassList
  case maybeClassList' of
    Nothing -> lift (assertFailure "Failed to load class")
    Just classList -> do
      let childVtnw = (head classList)
          parentVtnw = (head (tail classList))
      lift $ 
        evalStateT 
          (isSubtypeOf 
            (TypeCheckerClassRefType 
              (TypeCheckerClassReferenceTypeWrapper 
                childVtnw 
                  (if null childTypeArgs 
                    then Nothing
                    else (Just (V.fromList childTypeArgs))))) 
            (TypeCheckerClassRefType 
              (TypeCheckerClassReferenceTypeWrapper 
                parentVtnw 
                  (if null parentTypeArgs
                    then Nothing
                    else (Just (V.fromList parentTypeArgs))))))
          (classpath, M.empty)

test3 :: StateT ClassPath IO ()
test3 = do
  isSubtype <- subtypeTest "java/lang/Integer" "java/lang/Number"
  lift $ assertBool
    "java/lang/Integer is a subtype of java/lang/Number"
    isSubtype
  isNotSubType <- subtypeTest "java/lang/Number" "java/lang/Integer"
  lift $ assertBool
    "java/lang/Number is not a subtype of java/lang/Integer"
    (not isNotSubType)
      
test4 :: StateT ClassPath IO ()
test4 = do
  isSubtype <- subtypeTest "java/lang/Integer" "java/io/Serializable"
  lift $ assertBool
    "java/lang/Integer is a subtype of java/io/Serializable"
    isSubtype

test5 :: StateT ClassPath IO ()
test5 = do
  isSubtype <- subtypeTest "java/lang/Integer" "java/lang/Object"
  lift $ assertBool
    "java/lang/Integer is a subtype of java/lang/Object"
    isSubtype

test6 :: StateT ClassPath IO ()
test6 = do
  isSubtype <- subtypeTest "java/io/Serializable" "java/lang/Object"
  lift $ assertBool
    "java/io/Serializable is a subtype of java/lang/Object"
    isSubtype

test7 :: StateT ClassPath IO ()
test7 = do
  isSubtype <- subtypeTestWithTypeParams "java/util/List" [TypeCheckerTypeArgument Nothing createValidTypeRefTypeInteger] 
                            "java/util/Collection" [TypeCheckerTypeArgument Nothing createValidTypeRefTypeInteger]
  lift $ assertBool
    "java/util/List<Integer> is a subtype of java/util/Collection<Integer>"
    isSubtype

test8 :: StateT ClassPath IO ()
test8 = do
  isSubtype <- subtypeTestWithTypeParams "java/util/Vector" [TypeCheckerTypeArgument Nothing createValidTypeRefTypeInteger] 
                            "java/util/AbstractCollection" [TypeCheckerTypeArgument Nothing createValidTypeRefTypeInteger]
  lift $ assertBool
    "java/util/Vector<Integer> is a subtype of java/util/AbstractCollection<Integer>"
    isSubtype

test9 :: StateT ClassPath IO ()
test9 = do
  isSubtype <- subtypeTestWithTypeParams "java/util/Vector" [TypeCheckerTypeArgument Nothing createValidTypeRefTypeInteger] 
                            "java/util/List" [TypeCheckerTypeArgument Nothing createValidTypeRefTypeInteger]
  lift $ assertBool
    "java/util/Vector<Integer> is a subtype of java/util/List<Integer>"
    isSubtype

test10 :: StateT ClassPath IO ()
test10 = do
  let typeVarialbeRefType = TypeCheckerTypeVariableRefType (SimpleName (T.pack "R"))
  isSubtype <- subtypeTestWithTypeParams "java/util/Vector" [TypeCheckerTypeArgument Nothing typeVarialbeRefType] 
                            "java/util/AbstractCollection" [TypeCheckerTypeArgument Nothing typeVarialbeRefType]
  lift $ assertBool
    "java/util/Vector<R> is a subtype of java/util/AbstractCollection<R>"
    isSubtype

test11 :: StateT ClassPath IO ()
test11 = do
  classpath <- get
  maybeClassList <- sequence [getClass (T.pack "java/lang/Number"), getClass (T.pack "java/lang/Integer")]
  let maybeClassList' = sequence maybeClassList
  case maybeClassList' of
    Nothing -> lift (assertFailure "Failed to load class")
    Just classList -> do
      let numberVtnw = (head classList)
          integerVtnw = (head (tail classList))
          classRefTypeNumber = TypeCheckerClassRefType (TypeCheckerClassReferenceTypeWrapper numberVtnw Nothing)
          classRefTypeInteger = TypeCheckerClassRefType (TypeCheckerClassReferenceTypeWrapper integerVtnw Nothing)
      isSubtype <- subtypeTestWithTypeParams 
        "java/util/Vector" [TypeCheckerTypeArgument Nothing classRefTypeInteger] 
        "java/util/Vector" [TypeCheckerTypeArgument (Just ValidTypeWildcardIndicatorExtends) classRefTypeNumber]
      lift $ assertBool
        "java/util/Vector<Integer> is a subtype of java/util/Vector<? extends Number>"
        isSubtype

test12 :: StateT ClassPath IO ()
test12 = do
  classpath <- get
  maybeClassList <- sequence [getClass (T.pack "java/lang/Number"), getClass (T.pack "java/lang/Integer")]
  let maybeClassList' = sequence maybeClassList
  case maybeClassList' of
    Nothing -> lift (assertFailure "Failed to load class")
    Just classList -> do
      let numberVtnw = (head classList)
          integerVtnw = (head (tail classList))
          classRefTypeNumber = TypeCheckerClassRefType (TypeCheckerClassReferenceTypeWrapper numberVtnw Nothing)
          classRefTypeInteger = TypeCheckerClassRefType (TypeCheckerClassReferenceTypeWrapper integerVtnw Nothing)
      isSubtype <- subtypeTestWithTypeParams 
        "java/util/Vector" [TypeCheckerTypeArgument Nothing classRefTypeInteger] 
        "java/util/AbstractCollection" [TypeCheckerTypeArgument (Just ValidTypeWildcardIndicatorExtends) classRefTypeNumber]
      lift $ assertBool
        "java/util/Vector<Integer> is a subtype of java/util/AbstractCollection<? extends Number>"
        isSubtype

test13 :: StateT ClassPath IO ()
test13 = do
  classpath <- get
  maybeClassList <- sequence [getClass (T.pack "java/lang/Number"), getClass (T.pack "java/lang/Integer")]
  let maybeClassList' = sequence maybeClassList
  case maybeClassList' of
    Nothing -> lift (assertFailure "Failed to load class")
    Just classList -> do
      let numberVtnw = (head classList)
          integerVtnw = (head (tail classList))
          classRefTypeNumber = TypeCheckerClassRefType (TypeCheckerClassReferenceTypeWrapper numberVtnw Nothing)
          classRefTypeInteger = TypeCheckerClassRefType (TypeCheckerClassReferenceTypeWrapper integerVtnw Nothing)
      isNotSubtype <- not <$> subtypeTestWithTypeParams 
        "java/util/Vector" [TypeCheckerTypeArgument (Just ValidTypeWildcardIndicatorExtends) classRefTypeNumber] 
        "java/util/AbstractCollection" [TypeCheckerTypeArgument Nothing classRefTypeInteger]
      lift $ assertBool
        "java/util/Vector<? extends Number> is not a subtype of java/util/AbstractCollection<Integer>"
        isNotSubtype

test14 :: StateT ClassPath IO ()
test14 = do
  classpath <- get
  maybeClassList <- sequence [getClass (T.pack "java/lang/Number"), getClass (T.pack "java/lang/Integer")]
  let maybeClassList' = sequence maybeClassList
  case maybeClassList' of
    Nothing -> lift (assertFailure "Failed to load class")
    Just classList -> do
      let numberVtnw = (head classList)
          integerVtnw = (head (tail classList))
          classRefTypeNumber = TypeCheckerClassRefType (TypeCheckerClassReferenceTypeWrapper numberVtnw Nothing)
          classRefTypeInteger = TypeCheckerClassRefType (TypeCheckerClassReferenceTypeWrapper integerVtnw Nothing)
      isSubtype <- subtypeTestWithTypeParams 
        "java/util/Vector" [TypeCheckerTypeArgument Nothing classRefTypeNumber] 
        "java/util/AbstractCollection" [TypeCheckerTypeArgument (Just ValidTypeWildcardIndicatorSuper) classRefTypeInteger]
      lift $ assertBool
        "java/util/Vector<Number> is a subtype of java/util/AbstractCollection<? super Integer>"
        isSubtype

test15 :: StateT ClassPath IO ()
test15 = do
  classpath <- get
  maybeClassList <- sequence [getClass (T.pack "java/lang/Number"), getClass (T.pack "java/lang/Integer"), getClass (T.pack "java/util/List")]
  let maybeClassList' = sequence maybeClassList
  case maybeClassList' of
    Nothing -> lift (assertFailure "Failed to load class")
    Just classList -> do
      let numberVtnw = (head classList)
          integerVtnw = (head (tail classList))
          listVtnw = (head (tail (tail classList)))
          classRefTypeNumber = TypeCheckerClassRefType (TypeCheckerClassReferenceTypeWrapper numberVtnw Nothing)
          classRefTypeInteger = TypeCheckerClassRefType (TypeCheckerClassReferenceTypeWrapper integerVtnw Nothing)
      isSubtype <- subtypeTestWithTypeParams 
        "java/util/List" [TypeCheckerTypeArgument Nothing classRefTypeNumber] 
        "java/util/List" [TypeCheckerTypeArgument (Just ValidTypeWildcardIndicatorSuper) classRefTypeInteger]
      lift $ assertBool
        "java/util/Vector<Number> is a subtype of java/util/AbstractCollection<? super Integer>"
        isSubtype

main :: IO ()
main = do
  classPath <- createClassPath "out3/classes"
  defaultMain
    [ testCase "load class from classpath" (evalStateT test1 classPath)
    , testCase "super type set" (evalStateT test2 classPath)
    , testCase "class is parent subtype" (evalStateT test3 classPath)
    , testCase "class is interface subtype" (evalStateT test4 classPath)
    , testCase "class is object subtype" (evalStateT test5 classPath)
    , testCase "interface is object subtype" (evalStateT test6 classPath)
    , testCase "parameterized interface is interface subtype" (evalStateT test7 classPath)
    , testCase "parameterized class is class subtype" (evalStateT test8 classPath)
    , testCase "parameterized class is interface subtype" (evalStateT test9 classPath)
    , testCase "generic class is class subtype" (evalStateT test10 classPath)
    , testCase "paramaterized class is generic class with wildcard subtype" (evalStateT test11 classPath)
    , testCase "paramaterized class is generic super class with extends wildcard subtype" (evalStateT test12 classPath)
    , testCase "paramaterized class with wildcard is not generic super class subtype" (evalStateT test13 classPath)
    , testCase "paramaterized class is generic super class with super wildcard subtype" (evalStateT test14 classPath)
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
