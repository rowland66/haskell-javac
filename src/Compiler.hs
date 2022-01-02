module Compiler (
  compile
) where

import qualified Data.Map.Strict as Map
import Control.Monad (foldM,forM_)
import Control.Monad.Trans.State.Strict ( StateT(runStateT) )
import Text.Parsec.Error (newErrorMessage, Message(Message))
import Lexer
import Parser
import Parser2
import TypeChecker
import Text.ParserCombinators.Parsec hiding (token, tokens)
import System.Environment (getArgs)
import qualified System.FilePath.Glob as G
import ClassWriter ( writeClass )
import ClassPath ( ClassPath, createClassPath, getPackageClasses )
import Debug.Trace
import qualified Data.Text as T

type OptionMap = Map.Map String String

compile :: IO ()
compile = do
  args <- getArgs
  let (optionMap, fileGlobs) = getCommandLineOptions args
  srcFiles <- foldM (\l a -> fmap (l ++) (G.glob a)) [] fileGlobs
  classPath <- createClassPath (optionMap Map.! "-cp")
  let maybeDefaultNameToPackageMap = defaultNameToPackageMap classPath
  case maybeDefaultNameToPackageMap of
    Nothing -> print "Failed to find default Java types. Fix classpath and retry."
    Just m -> compile' optionMap classPath m srcFiles

compile' :: OptionMap -> ClassPath -> NameToPackageMap -> [FilePath] -> IO ()
compile' optionMap cp defaultNameMapping srcFiles = do
  print "Lexing and Parsing..."
  lexAndParseResult <- 
    foldM (\m file -> fmap (\eitherList -> (++) <$> eitherList <*> m) (lexAndParse optionMap defaultNameMapping file)) (Right []) srcFiles
  let parserResult = lexAndParseResult >>= parseClasses2
  case parserResult of
    Left e -> print e
    Right ast -> do
      print "Type Checking..."
      (eTypedClazzes, typeData) <- runStateT (typeCheck >> transform) (cp,ast)
      case eTypedClazzes of
        Left errorList -> displayTypeErrors errorList >> print ast
        Right typedClazzes -> do
          print "Writing Classes..."
          forM_ typedClazzes (writeClass (optionMap Map.! "-d"))
          print "Complete"

lexAndParse :: OptionMap -> NameToPackageMap -> FilePath -> IO (Either ParseError [Clazz])
lexAndParse optionMap defaultNameToPackageMap file = do
  lexResult <- tokenizeFromFile file
  cp <- createClassPath (optionMap Map.! "-cp")
  return $ lexResult >>= parseCompilationUnit cp defaultNameToPackageMap

getCommandLineOptions :: [String] -> (OptionMap, [String])
getCommandLineOptions args =
  let (_, optionMap, fileGlobs) = foldl (\(option, optionMap, fileGlobs) arg ->
                                    if not (null option) then
                                      ("", Map.insert option arg optionMap, fileGlobs)
                                    else
                                      if isCommandLineOption arg then
                                        (arg, optionMap, fileGlobs)
                                      else
                                        ("", optionMap, arg:fileGlobs)
                                  ) ("", Map.empty, []) args
  in
    (addDefaultOutput optionMap, fileGlobs)

isCommandLineOption :: String -> Bool
isCommandLineOption "-d" = True
isCommandLineOption "-cp" = True
isCommandLineOption _ = False

addDefaultOutput :: OptionMap -> OptionMap
addDefaultOutput mp =
  case mp Map.!? "-d" of
    Just _ -> mp
    Nothing -> Map.insert "-d" "." mp

mergeMaps :: Either ParseError (Map.Map String Clazz) -> Either ParseError (Map.Map String Clazz) -> Either ParseError (Map.Map String Clazz)
mergeMaps (Left es) _ = Left es
mergeMaps (Right es) (Left e) = Left e
mergeMaps (Right es) (Right e) = do
  let duplicateClass = foldr (\k b -> case b of
                                        Nothing -> if Map.member k es then Just (classError (e Map.! k) $ "Duplicate class: "++k) else Nothing
                                        Just e -> Just e)
                         Nothing (Map.keys e)
  case duplicateClass of
    Nothing -> Right (Map.union es e)
    Just e -> Left e

displayTypeErrors :: [TypeError] -> IO ()
displayTypeErrors = mapM_ (print)

classError :: Clazz -> String -> ParseError
classError (NewClazz pos _ _ _ _ _ _) str = newErrorMessage (Message str) pos

defaultNameToPackageMap :: ClassPath -> Maybe NameToPackageMap
defaultNameToPackageMap cp =
  let package = [T.pack "java", T.pack "lang"] in
  Map.fromList <$> fmap (fmap (\nm -> (nm, package))) (getPackageClasses cp package)
