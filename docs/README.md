# docs/ -- the north star

- `whitepaper.md` -- what clotran is, the four consulting scenarios it
  is aimed at, where each stands today (measured), and the road.
- `deck.md` -- the pitch deck: one `##` heading per slide.
- `deck.css`, `paper.css` -- the looks. A 16:9 page per section for the
  deck, A4 for the paper.

Edit the markdown; regenerate with

    make docs        # docs/whitepaper.pdf and docs/pitch-deck.pdf

which runs pandoc (markdown to HTML) and a headless Chrome or Chromium
(HTML to PDF). Nothing else is needed: no LaTeX. `CHROME=/path/to/it`
overrides the browser the Makefile finds. The PDFs are generated and
not committed; the markdown is the source of truth.

When a number in the paper or the deck changes, it changes because a
scorecard moved: cite the script that measured it.
