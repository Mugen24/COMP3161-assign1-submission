import MinHS.Parse
import MinHS.Syntax
import MinHS.TypeChecker
import MinHS.Pretty
import MinHS.Evaluator
import qualified Hindsight.Parse as HParse
import qualified Hindsight.Syntax as H
import qualified Hindsight.Pretty as HPretty
import qualified Hindsight.CBVCompile as CBV
import qualified Hindsight.CBNCompile as CBN
import qualified Hindsight.Evaluator as HEval
import qualified Hindsight.TypeChecker as TC
import qualified Hindsight.Optimiser as Opt
import Control.Monad
import Data.Either
import Data.Monoid((<>))
import Options.Applicative.Types
import Options.Applicative
import qualified Prettyprinter as PP (Pretty (..),Doc,unAnnotate)
import Prettyprinter.Render.Terminal (AnsiStyle(..),putDoc)

type Action a b = a -> Either (IO ()) b

type Doc = PP.Doc AnsiStyle

main = execParser argsInfo >>= main'
  where main' (pipeline, filter, mhs, cbn, types, opt, file) = (pipeline filter mhs cbn types opt <$> readFile file) >>= either id id

        argsInfo = info (helper <*> args)
                    (fullDesc <> progDesc "A interpreter for a small functional language"
                              <> header "MinHS - COMP3161 Concepts of Programming Languages")

        args =  (,,,,,,) <$> option readAction ( long "dump"
                               <> metavar "STAGE"
                               <> value (evaluatorAction)
                               <> help "stage after which to dump the current state. \n                           [parser,parser-raw,typechecker,evaluator,compiler,optimiser]")
                     <*> flag id PP.unAnnotate (long "no-colour"
                                     <> help "do not use colour when pretty printing")
                     <*> flag False True (long "minhs"
                                     <> help "accept MinHS input instead of hindsight")
                     <*> flag False True (long "cbn"
                                     <> help "Use CBNCompiler instead of CBVCompiler")
                     <*> flag True False (long "no-types"
                                     <> help "Skip type inference")
                     <*> flag False True (long "optimise"
                                     <> help "Use hindsight optimiser")
                     <*> argument str (metavar "FILE")

        readAction :: ReadM ((Doc -> Doc) -> Bool -> Bool -> Bool -> Bool -> Action String (IO ()))
        readAction = readerAsk >>= \x -> case x of
            "parser"      -> return $ \f mhs cbn types opt ->
              if mhs
              then parser >=> printer f
              else tparser >=> tpc >=> printer f
            "typechecker" -> return $ \f mhs cbn types opt ->
              if mhs
              then parser >=> typechecker f >=> printer f
              else tparser >=> tpc >=> ttypechecker f >=> printer f
            "optimiser" -> return $ \f mhs cbn types opt ->
              tparser >=> tpc >=> ttypechecker f >=> optimiser >=> printer f
            "parser-raw"  -> return $ \f mhs cbn types opt ->
              if mhs
              then parser >=> rawPrinter
              else tparser >=> tpc >=> rawPrinter
            "compiler" -> return $ \f mhs cbn types opt ->
              let compiler | cbn       = cbnCompiler
                           | otherwise = cbvCompiler
                  typecheck | types     = typechecker
                            | otherwise = const return
                  typecheck' | types     = ttypechecker
                             | otherwise = const return
                  optimise | opt       = optimiser
                           | otherwise = return
              in parser >=> typecheck f >=> compiler >=> optimise >=> typecheck' f >=> printer f
            "evaluator"   -> return $ evaluatorAction
            _             -> readerAbort (ShowHelpText Nothing)
        evaluatorAction :: (Doc -> Doc) -> Bool -> Bool -> Bool -> Bool -> Action String (IO ())
        evaluatorAction f mhs cbn types opt
          | mhs =
            let
              typecheck | types     = typechecker
                        | otherwise = const return
            in parser >=> typecheck f >=> evaluator cbn >=> printer f
          | otherwise =
            let
              typecheck | types     = ttypechecker
                        | otherwise = const return
              optimise | opt       = optimiser
                       | otherwise = return
            in tparser >=> tpc >=> typecheck f >=> optimise >=> tevaluator >=> printer f

        parser :: Action String Program
        parser = either (Left . putStrLn . show) Right . parseProgram ""

        tparser :: Action String HParse.PBind
        tparser = either (Left . putStrLn . show) Right . HParse.parseProgram ""

        tpc :: Action HParse.PBind H.Program
        tpc = either (Left . putStrLn) Right . HParse.toCBind

        typechecker :: (Doc -> Doc) -> Action Program Program
        typechecker f p | Just v <- typecheck p = Left . (>> putStrLn "") . putDoc . f . ansipp $ v
                        | otherwise             = Right $ p

        ttypechecker :: (Doc -> Doc) -> Action H.Program H.Program
        ttypechecker f p | Just v <- TC.typecheck p = Left . (>> putStrLn "") . putDoc . f . ansipp $ v
                         | otherwise             = Right $ p

        evaluator b = Right . evaluate b

        optimiser = Right . Opt.optimiser

        tevaluator = Right . HEval.evaluate

        cbvCompiler = Right . CBV.compileProgram

        cbnCompiler = Right . CBN.compileProgram

        rawPrinter :: (Show a) => Action a (IO ())
        rawPrinter = Right . putStrLn . show

        printer :: (ANSIPretty a) => (Doc -> Doc) -> Action a (IO ())
        printer filter = Right . (>> putStrLn "") . putDoc . filter . ansipp

        fromRight = either (error "fromRight on Left") id
