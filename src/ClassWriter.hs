module ClassWriter
  ( writeClass
  ) where

import Data.Binary.Put
import qualified Data.ByteString.Lazy as B
import qualified Data.ByteString.Builder as BSB
import Control.Monad.Trans.State
import TypeChecker
import qualified ConstantPoolBuilder as CPB
import ByteCodeBuilder
import System.IO (openFile,hClose,IOMode(..))
import System.Directory (createDirectoryIfMissing)
import qualified Data.Text as T
import TypeCheckerTypes

writeClass :: FilePath -> TypedClazz -> IO ()
writeClass outputDirectory clazz@(NewTypedClazz _ nameVtn _ _ _) = do
  let (packageText,nameText) = deconstructQualifiedName (getValidTypeQName nameVtn)
  let packageDirectory = (if null packageText then "" else sep++T.unpack (pathFromTextList packageText))
  createDirectoryIfMissing True (outputDirectory++packageDirectory)
  handle <- openFile (outputDirectory++packageDirectory++"/"++T.unpack nameText++".class") WriteMode
  B.hPut handle (buildClass clazz)
  hClose handle

pathFromTextList :: [T.Text] -> T.Text
pathFromTextList = T.intercalate textSep

textSep = T.pack "/"

sep = "/"
