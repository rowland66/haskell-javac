module ClassWriter
  ( writeClass
  ) where

import Data.Binary.Put
import qualified Data.ByteString.Lazy as B
import qualified Data.ByteString.Builder as BSB
import Control.Monad.Trans.State
import Parser2
import TypeChecker
import qualified ConstantPoolBuilder as CPB
import ByteCodeBuilder
import System.IO (openFile,hClose,IOMode(..))

writeClass :: FilePath -> TypedClazz -> IO ()
writeClass outputDirectory clazz@(NewTypedClazz name _ _ _ _) = do
  handle <- openFile (outputDirectory++"/"++name++".class") WriteMode
  B.hPut handle (buildClass clazz)
  hClose handle
