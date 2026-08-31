# Error report

## 2026-08-27 20:11 PDT — `blueprint/blueprint.tex`, lines 1261–1271

In the proof of \(\texttt{lem:localized-sobolev-decay}\), the auxiliary function is
defined as \(u := \kappa_k * g\) on line 1261, but the subsequent claims use the
undefined symbol \(\nu\). The three occurrences have been corrected to \(u\).

## 2026-08-27 20:13 PDT — `blueprint/blueprint.tex`, line 423

The estimate on line 412 is \(2\lVert w\rVert_1 + \lVert w''\rVert_1\).
Applying it to the preceding bounds for \(m\) therefore gives
\(2\cdot2^4 + 2^9\), rather than \(2^4 + 2^9\). The corrected bound remains
strictly smaller than \(2^{10}\), so the displayed statement and its constant
are unchanged.
