import qualified Data.Map.Strict as Map
import Control.Monad (foldM,forM_)
import Text.Parsec.Error (newErrorMessage, Message(Message))
import Lexer
import Parser
import Parser2
import TypeChecker
import Text.ParserCombinators.Parsec hiding (token, tokens)
import System.Environment (getArgs)
import System.FilePath.Glob
import ClassWriter

main :: IO ()
main = do
  args <- getArgs
  let (optionMap, fileGlobs) = getCommandLineOptions args
  srcFiles <- foldM (\l a -> (fmap (\files -> l ++ files) (glob a))) [] fileGlobs
  step1Result <- foldM (\m file -> (fmap (\eitherMap -> (mergeMaps m eitherMap)) (lexAndParse file))) (Right Map.empty) srcFiles
  let parserResult = step1Result >>= parseClasses2
  case parserResult of
    Left e -> putStrLn (show e)
    Right (ast) ->
      case (typeCheck ast) of
        Just errorList -> (displayTypeErrors errorList) >> (putStrLn (show ast))
        Nothing -> do
          let eTypedClazzes = transform ast
          case eTypedClazzes of
            Right typedClazzes -> forM_ typedClazzes (writeClass (optionMap Map.! "-d"))
            Left errorList2 -> (displayTypeErrors errorList2) >> (putStrLn (show ast))

lexAndParse :: FilePath -> IO (Either ParseError (Map.Map String Clazz))
lexAndParse file = do
  lexResult <- (tokenizeFromFile file)
  return $ lexResult >>= parseClasses

getCommandLineOptions :: [String] -> ((Map.Map String String), [String])
getCommandLineOptions args =
  let (_, optionMap, fileGlobs) = foldl (\(option, optionMap, fileGlobs) arg ->
                                    if (not (null option)) then
                                      ("", (Map.insert option arg optionMap), fileGlobs)
                                    else
                                      if (isCommandLineOption arg) then
                                        (arg, optionMap, fileGlobs)
                                      else
                                        ("", optionMap, arg:fileGlobs)
                                  ) ("", Map.empty, []) args
  in
    (addDefaultOutput optionMap, fileGlobs)

isCommandLineOption :: String -> Bool
isCommandLineOption "-d" = True
isCommandLineOption _ = False

addDefaultOutput :: (Map.Map String String) -> (Map.Map String String)
addDefaultOutput mp =
  case (mp Map.!? "-d") of
    Just _ -> mp
    Nothing -> (Map.insert "-d" "." mp)

mergeMaps :: (Either ParseError (Map.Map String Clazz)) -> (Either ParseError (Map.Map String Clazz)) -> (Either ParseError (Map.Map String Clazz))
mergeMaps (Left es) _ = Left es
mergeMaps (Right es) (Left e) = Left e
mergeMaps (Right es) (Right e) = do
  let duplicateClass = foldr (\k b -> case b of
                                        Nothing -> if (Map.member k es) then Just (classError (e Map.! k) $ "Duplicate class: "++k) else Nothing
                                        Just e -> Just e)
                         Nothing (Map.keys e)
  case duplicateClass of
    Nothing -> Right (Map.union es e)
    Just e -> Left e

getAst :: IO(Either ParseError (Map.Map String Clazz2))
getAst = do
  lexerResult <- tokenizeFromFile "./Test.java"
  return $ lexerResult >>= parseClasses >>= parseClasses2

displayTypeErrors :: [TypeError] -> IO ()
displayTypeErrors errorList = mapM_ (putStrLn . show) errorList

classError :: Clazz -> String -> ParseError
classError (NewClazz pos _ _ _ _ _) str = newErrorMessage (Message str) pos
