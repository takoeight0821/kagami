module Main where

import qualified Data.Text.IO as T
import qualified Malgo.Driver as Driver
import Malgo.Parser (parseMalgo)
import Malgo.Prelude hiding (value)
import Options.Applicative
import System.Directory (XdgDirectory (XdgData), getXdgDirectory)
import System.FilePath ((</>))
import System.FilePath.Lens (extension)
import Text.Megaparsec (errorBundlePretty)
import Text.Read (read)

main :: IO ()
main = do
  command <- parseCommand
  case command of
    ToLL opt -> do
      basePath <- getXdgDirectory XdgData ("malgo" </> "base")
      opt <- pure $ opt {modulePaths = modulePaths opt <> [".malgo-work" </> "build", basePath]}
      src <- T.readFile (srcName opt)
      let parsedAst = case parseMalgo (srcName opt) src of
            Right x -> x
            Left err -> error $ errorBundlePretty err
      Driver.compileFromAST parsedAst opt
    Build -> error "not implemented"

toLLOpt :: Parser Opt
toLLOpt =
  ( Opt
      <$> strArgument (metavar "SOURCE" <> help "Source file" <> action "file")
      <*> strOption
        ( long "output" <> short 'o' <> metavar "OUTPUT" <> value ""
            <> help
              "Write LLVM IR to OUTPUT"
        )
      <*> switch (long "dump-parsed")
      <*> switch (long "dump-renamed")
      <*> switch (long "dump-typed")
      <*> switch (long "dump-desugar")
      <*> switch (long "no-opt")
      <*> switch (long "no-lambdalift")
      <*> fmap read (strOption (long "inline" <> value "10"))
      <*> switch (long "debug-mode")
      <*> many (strOption (long "module-path" <> short 'M' <> metavar "MODULE_PATH"))
      <*> switch (long "force")
  )
    <**> helper

data Command
  = ToLL Opt
  | Build

parseCommand :: IO Command
parseCommand = do
  command <-
    execParser
      ( info (subparser toLL <|> subparser build <**> helper) $
          fullDesc
            <> header "malgo programming language"
      )
  case command of
    ToLL opt ->
      if null (dstName opt)
        then pure $ ToLL $ opt {dstName = srcName opt & extension .~ ".ll"}
        else pure command
    Build -> pure Build
  where
    toLL =
      command "to-ll" $
        info (ToLL <$> toLLOpt) $
          fullDesc
            <> progDesc "Compile Malgo file (.mlg) to LLVM Textual IR (.ll)"
            <> header "malgo to LLVM Textual IR Compiler"
    build =
      command "build" $
        info (pure Build) $
          fullDesc
            <> progDesc "Build Malgo project"
            <> header "malgo build"
