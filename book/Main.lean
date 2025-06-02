import VersoManual
import FPLean

open Verso.Genre Manual
open Verso Code External

def config : Config where
  emitTeX := false
  emitHtmlSingle := false
  emitHtmlMulti := true
  htmlDepth := 2
  extraFiles := [("static", "static")]
  extraCss := [
    "/static/theme.css",
    "/static/fonts/source-serif/source-serif-text.css",
    "/static/fonts/source-code-pro/source-code-pro.css",
    "/static/fonts/source-sans/source-sans-3.css",
    "/static/fonts/noto-sans-mono/noto-sans-mono.css"
  ]
  logo := some "/static/lean_logo.svg"
  sourceLink := some "https://github.com/leanprover/fp-lean"
  issueLink := some "https://github.com/leanprover/fp-lean/issues"
def main := manualMain (%doc FPLean) (config := config.addKaTeX)
