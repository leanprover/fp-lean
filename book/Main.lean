import VersoManual
import FPLean

open Verso.Genre Manual
open Verso Code External

open Verso.Output.Html in
def plausible := {{
    <script defer="defer" data-domain="lean-lang.org" src="https://plausible.io/js/script.outbound-links.js"></script>
  }}


def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2
  extraFiles := [("static", "static")]
  extraCss := [
    "/static/theme.css",
    "/static/fonts/source-serif/source-serif-text.css",
    "/static/fonts/source-code-pro/source-code-pro.css",
    "/static/fonts/source-sans/source-sans-3.css",
    "/static/fonts/noto-sans-mono/noto-sans-mono.css"
  ]
  extraHead := #[plausible]
  logo := some "/static/lean_logo.svg"
  sourceLink := some "https://github.com/leanprover/fp-lean"
  issueLink := some "https://github.com/leanprover/fp-lean/issues"

/--
A script for redirecting a page to its canonical URL.

The Web host rewrites URLs to recover from 404s, so a URL like `monads.html` matches
`Monads/index.html` on disk and that content is served, which breaks relative URLs. This script
sends such a rewritten URL to the page's canonical address.

`canonical` is the page's path relative to the root of the generated site, ending in a slash. A URL
whose final segments reach the page by another route is rewritten to `canonical`: it may name the
page as a file ending in `.html` or `/index.html`, spell those segments in another case, or omit the
trailing slash. Any other URL is left alone.
-/
private def canonicalRedirectScript (canonical : String) : String :=
r#"<script>
(function () {
  const canonical = "# ++ canonical.quote ++ r#";
  const loc = window.location;
  const path = loc.pathname;

  // Normalize the path by which the page was accessed to the directory form
  // that canonical URLs use
  let dir = path;
  if (dir.endsWith("/index.html")) {
    dir = dir.slice(0, -"index.html".length);
  } else if (dir.endsWith(".html")) {
    dir = dir.slice(0, -".html".length) + "/";
  } else if (!dir.endsWith("/")) {
    dir = dir + "/";
  }

  // The prefix depends on where the site is served from, so compare only the
  // final segments, modulo case. Leave any other URL as it is.
  if (dir.slice(-canonical.length).toLowerCase() !== canonical.toLowerCase()) return;

  // The final segments did match, so redirect to the correct location,
  // taking into account that we might be served from a different root.
  const target = dir.slice(0, -canonical.length) + canonical;
  if (target !== path) {
    loc.replace(target + loc.search + loc.hash);
  }
})();
</script>"#

/--
Adds the canonical-URL redirect to every page in a generated site.

A host that serves a page from a URL other than the one it was generated for leaves the page's
`base` element pointing at the wrong directory, so its stylesheets, scripts, and links resolve
against the wrong prefix. The script goes first in the `head`, ahead of those references.

The page's own path is the part that varies, so each page gets its own copy of the script.
-/
private partial def addCanonicalRedirects (dir : System.FilePath) (canonical : String) : IO Unit := do
  let page := dir / "index.html"
  if !canonical.isEmpty && (← page.pathExists) then
    let html ← IO.FS.readFile page
    IO.FS.writeFile page <| html.replace "<head>" ("<head>" ++ canonicalRedirectScript canonical)
  for entry in ← dir.readDir do
    if ← entry.path.isDir then
      addCanonicalRedirects entry.path (canonical ++ entry.fileName ++ "/")

open Verso.Genre.Manual in
private def canonicalRedirects : ExtraStep := fun mode config _ _ =>
  match mode with
  | .multi => addCanonicalRedirects (config.destination / "html-multi") ""
  | .single => pure ()

def main := manualMain (%doc FPLean) (config := config) (extraSteps := [canonicalRedirects])
