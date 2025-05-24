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
  extraCss := ["/static/theme.css"]

def main := manualMain (%doc FPLean) (config := config.addKaTeX)
